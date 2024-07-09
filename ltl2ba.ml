open Printexc
open Sys
open Printf

let () = Printexc.record_backtrace true


type etat = int
type lettre = int

type formule = True 
              | False
              | Vide
              | P of int
              | Non of formule
              | Et of formule * formule
              | Ou of formule * formule
              | Implique of formule * formule
              | G of formule
              | F of formule
              | R of formule * formule
              | U of formule * formule
              | X of formule

(*===================================*)

let rec nnf (f:formule):formule = 
  match  f with 
    | G g -> nnf ( Non (F (Non g)) )
    | F g -> nnf ( U (True, g))
    | Implique (g,h) -> nnf ( Ou (Non g, h))
    | Et (g,h) -> let g' = nnf g in
                  let h' = nnf h in
                  Et (g',h')
    | Ou (g,h) -> let g' = nnf g in
                  let h' = nnf h in
                  Ou (g',h')
    | R (g,h) -> let g' = nnf g in
                 let h' = nnf h in
                 R (g',h')
    | U (g,h) -> let g' = nnf g in
                 let h' = nnf h in
                 U (g',h')
    | X g -> let g' = nnf g in X g'
    | Non f' -> begin match f' with
                      | G g -> nnf (Non ( Non (F (Non g)) ))
                      | F g -> nnf (Non ( U (True, g)))
                      | Implique (g,h) -> nnf (Non ( Ou (Non g, h)))
                      | Et (g,h) -> nnf (Ou (Non g,Non h))
                      | Ou (g,h) -> nnf (Et (Non g, Non h))
                      | R (g,h) -> nnf (U (Non g, Non h))
                      | U (g,h) -> nnf (R (Non g, Non h))
                      | Non g -> nnf g
                      | X g -> nnf (X (Non g))
                      | False -> True
                      | True -> False
                      | P i -> Non (P i)
                      |Vide -> Vide
                end
    | True -> True
    | False -> False
    | P i -> P i
    | Vide -> Vide

let rec max_var f =
    match f with 
    | G g | F g | Non g | X g -> max_var g 
    | Implique (g,h) | Et (g,h) | Ou (g,h) | R (g,h) | U (g,h) -> max (max_var g) (max_var h) 
    | False | True | Vide -> - 1
    | P i -> i


type pre_graph =
  {nb_nodes : int ;
  nb_var : int ;           (*les var sont numérotés de 0 à nb_var - 1*)
  incoming: (int, int list) Hashtbl.t;
  now: (int, formule list) Hashtbl.t ;
  next: (int, formule list) Hashtbl.t}


let create_pre_graph (f:formule):pre_graph = 
  let nb_var = max_var f + 1 in 
  let max_id = ref 0 in
  let incoming_f = Hashtbl.create 30 in  (* l'id en clé et une liste d'id en valeur*)
  let now_f = Hashtbl.create 30 in       (* l'id en clé et une liste de formule en valeur*)
  let next_f = Hashtbl.create 30 in      (* l'id en clé et une liste de formule en valeur*)
 
  let rec expand (curr:formule list) (old:formule list) (next:formule list) (incoming:int list) = 
    match curr with 
    |[] -> (* verif que il n'y a pas déjà un état avec les mêmes obligations*)
          let is_already_same_node = ref false in 
          let id = ref 1 in 
          while !id <= !max_id && not !is_already_same_node do
            if (begin match Hashtbl.find_opt next_f !id, Hashtbl.find_opt now_f !id with 
                  |None, None -> next = [] && old = []
                  |None, Some l' -> next = [] && old = l'
                  |Some l, None -> next = l && old = []
                  |Some l, Some l' -> next = l && old = l'
                end ) (*revient à : est ce que un node a deja les meme caractéristiques *)
            then (
              begin match Hashtbl.find_opt incoming_f !id with
                    |None -> Hashtbl.add incoming_f !id incoming
                    |Some l -> Hashtbl.replace incoming_f !id (incoming@l)
              end ;
              is_already_same_node := true
            ) ;
            incr id
          done;
          if not !is_already_same_node then ( (* création d'un nouveau noeud)*)
            let new_id = !max_id + 1 in
            incr max_id ;
            Hashtbl.add now_f  new_id old ;
            Hashtbl.add next_f new_id next ;
            Hashtbl.add incoming_f new_id incoming ;
            expand next [] [] [new_id]
          )
    |g::curr' ->  if List.mem g old then ( expand curr' old next incoming )
                  else (
                    match g with
                    | True | False | P _ | Non (P _) -> 
                            if g = False || List.mem (Non g) old then ()
                            else expand curr' (g::old) next incoming
                    | Et (g1,g2) -> expand (g1::g2::curr') (g::old) next incoming
                    | Ou (g1,g2) -> expand (g2::curr') (g::old) next incoming ;
                                    expand (g1::curr') (g::old) next incoming
                    | U (g1,g2) -> expand (g1::curr') (g::old) (g::next) incoming ;
                                    expand (g2::curr') (g::old) next incoming
                    | R (g1,g2) -> expand (g2::curr') (g::old) (g::next) incoming ;
                                    expand (g1::g2::curr') (g::old) next incoming
                    | X g1 -> expand curr' (g::old) (g1::next) incoming
                    | _ -> failwith "not an nnf"
                  )
  in
  expand [f] [] [] [0] ;
  {nb_nodes = !max_id + 1 ; nb_var = nb_var ; incoming = incoming_f ; now = now_f ; next = next_f}


(*======================================*)

type gba =
  {n : int;
  p : int ; (*nombre de variable propositionelles = taille des tableaux des transitions*)
  init : etat;
  nb_final_sets : int ;(*les id_set vont de 0 à nb_final_sets - 1*)
  term : int list array;   (* de taille n / term.(q) sont les final_set a qui q appartient *)
  delta : (etat, (bool array, etat) Hashtbl.t) Hashtbl.t}



let add_set_final (g:formule) (h:formule) (t: int list array) (pg:pre_graph) (id_set:int)= 
  for i = 1 to pg.nb_nodes - 1 do 
    begin match Hashtbl.find_opt pg.now i with 
          |None -> t.(i) <- id_set::t.(i)
          |Some l -> let found = ref false in  
                    let rec search l = match l with
                      |[] -> not !found
                      |x::xs -> if x = h then true
                            else ((if x = U(g,h) then found := true) ; search xs )
                    in
                    if search l then t.(i) <- id_set::t.(i)
                    (* revient à : if List.mem h l || not ( List.mem (U(g,h)) l ) then ...*)
    end
    done


let final_tab (f:formule) (pg:pre_graph) = 
  let final = Array.make pg.nb_nodes [] in
  let already_found = ref [] in
  let number_sets = ref 0 in
  let rec aux f =
    match f with
    | True| False | P _ | Vide | Non (P _ ) -> ()   
    | X g -> aux g
    | Et (g,h) | Ou (g,h) | R (g,h) -> aux g ; aux h
    | U (g,h) -> (if not (List.mem ((g,h)) !already_found) then (
                        already_found := (g,h)::!already_found ; add_set_final g h final pg !number_sets ; incr number_sets
                        ) 
                  ) ;
                  aux g ; aux h  
    | _ -> failwith "not an nnf" 
  in 
  aux f ;
  if !already_found = [] then (
    for i = 0 to pg.nb_nodes - 1 do 
      final.(i) <- [0] 
    done;
    number_sets := 1
  ) ;
  final, !number_sets


let pre_graph_to_gba (pg:pre_graph) (f:formule) = 
  print_endline "g commencé pg_to_ba" ;
  let init = 0 in 
  let n = pg.nb_nodes in  
  let p = pg.nb_var in 
  let delta = Hashtbl.create n in
  for i = 1 to n - 1 do 
    let v = Array.make p false in 
    let vus = Array.make p false in 
    if Hashtbl.mem pg.now i then (
      List.iter (fun g -> 
        match g with
          |P j -> v.(j) <- true ; vus.(j) <- true
          |Non (P j) -> (*v.(j) <- false *) vus.(j) <- true 
          | _ -> ()
        ) (Hashtbl.find pg.now i)
    ) ;
    let rec add valu j incom = 
      if j = p then (
        List.iter (fun id ->
                      match Hashtbl.find_opt delta id with
                      |None -> let h = Hashtbl.create n in 
                              Hashtbl.add h valu i ;
                              Hashtbl.add delta id h
                      |Some h -> Hashtbl.add h valu i
        ) incom
      )
      else if not vus.(j) then ( 
          let valu1 = Array.copy valu in 
          let valu2 = Array.copy valu in
          valu1.(j) <- false ; valu2.(j) <- true ; 
          add valu1 (j+1) incom ; add valu2 (j+1) incom ; 
      )
      else add valu (j+1) incom 
    in
    match Hashtbl.find_opt pg.incoming i with
    |None -> ()
    |Some l -> add v 0 l
  done ;
  let term, nb_sets = final_tab f pg in 
  {n = n ; p = pg.nb_var ; init = init ; nb_final_sets = nb_sets ; term = term ; delta = delta}


(*======================================*)


let incremente (t:bool array):bool array =
  let n = Array.length t in
  let t' = Array.copy t in 
  let i = ref 0 in
  while !i < n && t'.(!i) do
    t'.(!i ) <- false;
    incr i
  done;
  if !i < n then (t'.(!i) <- true ; t')
  else (printf "pas cool\n"; t')
  
let rec puissance_2 n = 
  assert (n >= 0) ;
  if n = 0 then 1 else 2*puissance_2 (n-1)


let build_set (g: gba) (s:int list) (v:bool array) =
  let t = Array.make g.n false in
  let process_state q =
    match Hashtbl.find_opt g.delta q with 
      |None -> ()
      |Some h -> List.iter (fun q' -> t.(q') <- true) (Hashtbl.find_all h v) 
  in
  List.iter process_state s;
  (* convert t to an ordered list of states *)
  let new_set = ref [] in
  for q = g.n - 1 downto 0 do
    if t.(q) then new_set := q :: !new_set
  done;
  !new_set


let powerset (g : gba) : gba =
  (*clé = une list d'état de g , valeur = l'indice associé dans l'automate des parties*)
  let sets = Hashtbl.create g.n in
  Hashtbl.add sets [0] 0;

  let last_set = ref 0 in
  let delta' = Hashtbl.create g.n in 

  (*renvoie (b,i) où b est vraie ssi s est deja présent dans sets et i l'indice du set s (nouveau si il n'éxistait pas déjà)*)
  let add_set s =
    try (false, Hashtbl.find sets s)
    with
    | Not_found -> incr last_set;
                   Hashtbl.add sets s !last_set;
                   (true, !last_set) 
  in
  
  (*DFS où s est une liste d'état de g et i son indice associé*)
  let rec explore s i =
    let v = ref (Array.make g.p false) in 
    for c = 1 to puissance_2 g.p  do
      let new_set = build_set g s !v in
      if new_set <> [] then (
        let is_new, j = add_set new_set in
        begin match Hashtbl.find_opt delta' i with
              |None -> let hi = Hashtbl.create g.n in 
                        Hashtbl.add hi !v j ;
                        Hashtbl.add delta' i hi
              |Some h -> Hashtbl.add h !v j 
        end ;
        if is_new then explore new_set j 
      ) ;
      v := incremente !v 
    done 
  in
  explore [0] 0;

  let n' = !last_set + 1 in
  
  let rec final_set = function
    | [] -> []
    | q :: qs -> g.term.(q) @ final_set qs 
  in
  let term' = Array.make n' [] in
  Hashtbl.iter (fun s i -> term'.(i) <- final_set s) sets ;
  {n = n' ; p = g.p ;init = 0 ; nb_final_sets = g.nb_final_sets ; term = term' ; delta = delta'}


type ba =
  {n : int;
  p :int ;
  init : etat;
  term : bool array;
  delta : (etat, (bool array, etat) Hashtbl.t) Hashtbl.t}

let gba_to_ba (g:gba):ba = 
  let n = g.n in  
  let n' = n * g.nb_final_sets in 
  
  (*transition*)
  let delta' = Hashtbl.create n' in 
  Hashtbl.iter ( fun q h ->
    let q_set = g.term.(q) in 
    for i = 0 to g.nb_final_sets - 1 do 
      let hi = Hashtbl.create n in            (*   table de hachage de q + n*i    *)
      let i_arrivee = if List.mem i q_set then (i + 1) mod g.nb_final_sets else i in (*est ce qu'on change de copie ou non*)

      Hashtbl.iter (fun v q' ->  
          Hashtbl.add hi v (q' + n*i_arrivee)
      ) h ;

      Hashtbl.add delta' (q + n*i) hi
    done
  ) g.delta ;

  (*accepting states*)
  let term' = Array.make n' false in 
  (* Il faut vérif qu'on parcourt une infinité de fois la boucle donc 
     il suffit de se mettre à un endroit de la boucle et regarder si qqun passe une infinité de fois.
     On choisit le premier maillon F1.*)
  for q = 0 to n - 1 do 
    if List.mem 0 g.term.(q) then term'.(q) <- true 
  done;

  let init' = g.init in  (* init + 0*n mais idem on pourrait choisir le init d'une autre copie*)

  {n = n' ; p = g.p ; init = init' ; term = term' ; delta = delta'}


(*=====================================*)

let cross_product_buchi (a:ba) (b:ba):ba = 
  assert (a.p = b.p) ;
  let n' = 2 * a.n * b.n in 
  
  (*transitions*)
  let delta' = Hashtbl.create n' in 
  for qa = 0 to a.n - 1 do 
    for qb = 0 to b.n - 1 do
      let hqa = Hashtbl.find a.delta qa in 
      let hqb = Hashtbl.find b.delta qb in 
      let hqaqb1 = Hashtbl.create a.n in
      let hqaqb2 = Hashtbl.create a.n in 
      Hashtbl.iter (fun v qa' ->
        if Hashtbl.mem hqb v then (
          let qb' = Hashtbl.find hqb v in 
          if a.term.(qa) then Hashtbl.add hqaqb1 v (a.n*b.n + qa' + a.n*qb') (*on passe du 1 vers le 2*)
          else Hashtbl.add hqaqb1 v (qa' + a.n*qb') ;                        (*on reste dans le 1*)
          if  b.term.(qb) then Hashtbl.add hqaqb2 v ( qa' + a.n*qb')           (*on passe du 2 vers le 1*)
          else Hashtbl.add hqaqb2 v (a.n*b.n + qa' + a.n*qb')                  (*on reste dans le 2*)
         )
      ) hqa ;
      Hashtbl.add delta' (qa + a.n*qb) hqaqb1 ;
      Hashtbl.add delta' (a.n*b.n + qa + a.n*qb) hqaqb2
    done;
  done;

  (*final*)
  let term' = Array.make n' false in 
  for qa = 0 to a.n - 1 do 
    if a.term.(qa) then (
      for qb = 0 to b.n - 1 do 
        term'.(qa + a.n*qb) <- true     (*on choisit de mettre le péage à la copie 1*)
      done
    )
  done;

  (*init*)
  let init' = a.init + a.n * b.init in    (*pareil on choisit la première copie*)

  {n = n' ; p = a.p ; init = init' ; term = term' ; delta = delta'}

(*========================*)

type ks =  (*kripke structure *)
  {n : etat ;
  p : int ;              (*nombre de variables propositionelles*)
  init : bool array; 
  r : bool array array;   (*matrice d'adjacence*)
  lab : bool array array} (*un array de taille n de bool array de taille p*)

let ks_to_ba (m:ks) = 
  let init' = 0 in 
  let n' = m.n + 1 in (*on rajouter un init qui pointe vers tout les anciens init*)
  let delta' = Hashtbl.create n' in

  for i = 0 to m.n - 1 do 
    let hi = Hashtbl.create n' in (*table de hachage des voisins du sommet i*)
    for j = 0 to m.n - 1 do 
      if m.r.(i).(j) then (
        let v = m.lab.(j) in
        Hashtbl.add hi v (j+1)
      )
    done;
    Hashtbl.add delta' (i+1) hi 
  done;
  (*cas paritculier du nouveau init créé*)
  let h0 = Hashtbl.create n' in 
  for i = 0 to m.n - 1 do 
    if m.init.(i) then (
      let v = m.lab.(i) in
      Hashtbl.add h0 v (i+1)
    )
  done;
  Hashtbl.add delta' init' h0 ;

  let term' = Array.make n' true in 

  {n = n' ; p = m.p ; init = init' ; term = term' ; delta = delta'}

(*==================================*)


exception LassoTrouve of int list
let language (a:ba) = (*None = language vide / Some l = l est un exemple de mot acceptant*)
  (*premier parcours*)
  let vus = Array.make a.n false in 
  let po = ref [] in (*parcours depuis init jusqu'au états terminaux accessibles en post_ordre*)
  let rec dfs x acc =
    if not vus.(x) then (
      vus.(x) <- true ;
      begin 
        match Hashtbl.find_opt a.delta x with 
        |None -> ()
        |Some h -> Hashtbl.iter (fun v y -> dfs y (v::acc)) h 
      end ;
      if a.term.(x) then po := (x,acc)::!po
    ) 
  in
  dfs a.init [] ;

  (*deuxième pour trouver le lasso*)
  let vus2 = Array.make a.n false in 
  let rec lasso_search x cible acc = 
    vus2.(x) <- true ;
    begin
      match Hashtbl.find_opt a.delta x with 
        |None -> ()
        |Some h -> Hashtbl.iter (fun v y -> 
                    if y = cible then raise (LassoTrouve (v::acc) )
                    else if not vus2.(y) then lasso_search y cible (v::acc)
                  ) h 
    end ;
  in
  try
    List.iter (fun (x,l) -> lasso_search x x begin match l with 
                        |[] -> failwith "error"
                        |hd::tl -> lasso_search x x (-1::tl)
                        end
              ) (List.rev !po) ;
    None
  with
  |LassoTrouve lasso -> Some (List.rev lasso)
