open Printexc
open Sys
open Printf
open Ltl2ba

let () = Printexc.record_backtrace true


let is_var_valide (f:formule) = 
  let p = max_var f + 1 in 
  let t = Array.make p false in 
  let rec aux f = 
    match f with
    | True | False | Vide -> ()
    | P i -> t.(i) <- true
    | Non g | F g | G g | X g -> aux g
    | Et (g,h)| Ou (g,h) | Implique (g,h) | R (g,h) | U (g,h) -> aux g ; aux h
  in
  aux f ; 
  let i = ref 0 in 
  while !i < p && t.(!i) = true do
    incr i 
  done;
  !i = p

let rec print_formule f = 
  match f with
  | True -> printf "True"
  | False -> printf "False"
  | P i -> printf "P %d" i 
  | Non g -> printf "Non ( " ; print_formule g ; printf " )"
  | Et (g,h) -> printf "( " ; print_formule g ; printf " ) Et ( " ; print_formule h ; printf " )"
  | Ou (g,h) -> printf "( " ; print_formule g ; printf " ) Ou ( " ; print_formule h ; printf " )"
  | Implique (g,h) -> printf "( " ; print_formule g ; printf " ) Implique ( " ; print_formule h ; printf " )"
  | G g -> printf "G ( " ; print_formule g ; printf " )" 
  | F g -> printf "F ( " ; print_formule g ; printf " )" 
  | R (g,h) -> printf "( " ; print_formule g ; printf " ) R ( " ; print_formule h ; printf " )"
  | U (g,h) -> printf "( " ; print_formule g ; printf " ) U ( " ; print_formule h ; printf " )"
  | X g -> printf "X ( " ; print_formule g ; printf " )" 
  | Vide -> printf "Vide"



let print_pre_graph (pg:pre_graph) = 
  printf "\n========================\n\n" ;
  printf "number nodes : %d\n" pg.nb_nodes ;
  printf "number var : %d\n\n" pg.nb_var ;
  let sort l = List.sort (fun x y -> x - y ) l in

  let incoming = Array.make pg.nb_nodes [] in 
  let now = Array.make pg.nb_nodes [] in 
  let next = Array.make pg.nb_nodes [] in 

  Hashtbl.iter (fun id l -> incoming.(id) <- sort l) pg.incoming ; 
  Hashtbl.iter (fun id l -> now.(id) <- l) pg.now ; 
  Hashtbl.iter (fun id l -> next.(id) <- l) pg.next ; 

  for i = 0 to pg.nb_nodes - 1 do 
    printf "%d :\n\t" i ;
    printf "incoming : " ; List.iter (fun j -> printf "%d , " j) incoming.(i) ; printf "\n\t" ;
    printf "now : " ;List.iter (fun f -> print_formule f ; printf " , ") now.(i) ; printf "\n\t" ;
    printf "next : " ;List.iter (fun f -> print_formule f ; printf " , ") next.(i) ; printf "\n\n"
  done ;
  printf "========================\n"


let print_bool_tab t =
  let len = Array.length t in 
  printf "[" ; 
  for i = 0 to  len - 2 do 
    printf " %d," (if t.(i) then 1 else 0) ;
  done;
  printf " %d ] " (if t.(len - 1) then 1 else 0)


let print_int_tab t = 
  let len = Array.length t in 
  printf "[" ; 
  for i = 0 to  len - 2 do 
    printf " %d," t.(i) ;
  done;
  printf " %d ] " t.(len - 1)

let print_int_list l = 
  let rec aux = function
    |[] -> printf "]\n" 
    |[x] -> printf "%d ]\n" x 
    |x::xs -> printf "%d ; " x ; aux xs 
  in
  printf "[ " ;
  aux l 

let print_list_tab t = 
  for i = 0 to Array.length t - 1 do
    printf "\t%d : " i ; print_int_list t.(i) 
  done

let print_gba (g:gba) =
  printf "========================\n\n" ;
  printf "nombre d'états : %d\n" g.n ; 
  printf "nombre de variable propositionelles : %d\n" g.p ; 
  printf "état initial : %d\n" g.init ;
  printf "états terminaux : \n" ; print_list_tab g.term ; printf "\n\n" ;
  let all_about_x x h = 
    printf "%d :\n" x ;
    Hashtbl.iter (fun v y ->
      printf "\t --- ";
      print_bool_tab v ;
      printf "-->  %d \n" y 
    ) h 
  in
  printf "transitions : \n" ;
  Hashtbl.iter all_about_x g.delta ;
  printf "========================\n" 


let print_ba (g:ba) =
  printf "========================\n\n" ;
  printf "nombre d'états : %d\n" g.n ; 
  printf "nombre de var : %d\n" g.p ; 
  printf "état initial : %d\n" g.init ;
  printf "états terminaux : " ; print_bool_tab g.term ; printf "\n\n" ;
  let all_about_x x h = 
    printf "%d :" x ;
    let h = Hashtbl.find g.delta x in 
    Hashtbl.iter (fun v y ->
      printf "\t --- ";
      print_bool_tab v ;
      printf "-->  %d \n" y 
    ) h 
  in 
  printf "transitions : \n" ;
  Hashtbl.iter all_about_x g.delta ;
  printf "========================\n" 


let print_ks (m:ks) = 
  printf "======================\n\n" ;
  printf "nombre d'états : %d\nnombre de variables propositionelles : %d\n" m.n m.p ;
  printf "états initiaux : numéro " ;
  for i = 0 to m.n - 1 do 
    if m.init.(i) then printf "%d " i 
  done;
  printf "\ntransitions :" ;
  for q = 0 to m.n - 1 do
    printf "\n%d " q ; print_bool_tab m.lab.(q) ; 
    for q' = 0 to m.n - 1 do
      if m.r.(q).(q') then printf "\n\t-------------> %d" q'
    done
  done;
  printf "\n\n==============\n" 

let rec print_lasso l = 
  match l with
  |[] -> failwith "error"
  |[x] -> printf "%d //\n" x
  |h::t -> (if h = -1 then printf "// " else printf "%d --> " h) ; print_lasso t

(*////////////////// test ///////////////////*)

let ba1 = 
  let h0 = Hashtbl.create 2 in 
  Hashtbl.add h0 [|true ; false|] 1 ;
  Hashtbl.add h0 [|false; true|] 0 ;
  let h1 = Hashtbl.create 2 in 
  Hashtbl.add h1 [|true ; false|] 0 ;
  Hashtbl.add h1 [|false; true|] 0 ;
  let h = Hashtbl.create 2 in 
  Hashtbl.add h 0 h0 ;
  Hashtbl.add h 1 h1 ;
  {n = 2 ; p = 2 ;init = 0 ; term = [|false; true|] ; delta = h}

let ba2 = 
  let h0 = Hashtbl.create 2 in 
  Hashtbl.add h0 [|true ; false|] 1 ;
  Hashtbl.add h0 [|false; true|] 0 ;
  let h1 = Hashtbl.create 1 in 
  Hashtbl.add h1 [|false ; true|] 0 ;
  let h = Hashtbl.create 2 in 
  Hashtbl.add h 0 h0 ;
  Hashtbl.add h 1 h1 ;
  {n = 2 ; p = 2 ; init = 0 ; term = [|true; false|] ; delta = h}

let test_cross_product_buchi () = (*succeeded - cf photo/dossier tipe*)
  print_ba ba1 ; 
  print_ba ba2 ;
  print_ba (cross_product_buchi ba1 ba2)


let test_nnf () = (*succeeded - cf LTL2BA & taiwan univ*)
  print_formule ( nnf (G (Implique (P 1, F (P 2))))) ; printf "\n" ;
  print_formule (nnf (Non (R (P 1,P 2)))) ; printf "\n"



let gba1:gba = 
  let h0 = Hashtbl.create 3 in 
  Hashtbl.add h0 [|true ; false|] 1 ;
  Hashtbl.add h0 [|false ; true|] 2 ; 
  Hashtbl.add h0 [|true ; true|] 0 ;
  let h1 = Hashtbl.create 1 in 
  Hashtbl.add h1 [|true ; true|] 0 ;
  let h2 = Hashtbl.create 1 in
  Hashtbl.add h2 [|true ; true|] 0 ; 
  let h = Hashtbl.create 3 in 
  Hashtbl.add h 0 h0 ;
  Hashtbl.add h 1 h1 ;
  Hashtbl.add h 2 h2 ;
  {n = 3 ; p = 2 ; init = 0 ; nb_final_sets = 2 ; term = [| [] ; [0] ; [1]|] ; delta = h}

let gba1bis:gba = (*quasi le meme mais avec 2 états acceptants par groupe d'acceptants*)
  let h0 = Hashtbl.create 5 in 
  Hashtbl.add h0 [|true ; false ; false ; false|] 1 ;
  Hashtbl.add h0 [|false ; true ; false ; false|] 2 ; 
  Hashtbl.add h0 [|false ; false ; true ; false|] 3 ; 
  Hashtbl.add h0 [|false ; false ; false ; true|] 4 ; 
  Hashtbl.add h0 [|true ; true ; true ; true|] 0 ;
  let h1 = Hashtbl.create 1 in 
  Hashtbl.add h1 [|true ; true ; true ; true|] 0 ;
  let h2 = Hashtbl.create 1 in
  Hashtbl.add h2 [|true ; true ; true ; true|] 0 ; 
  let h3 = Hashtbl.create 1 in 
  Hashtbl.add h3 [|true ; true ; true ; true|] 0 ;
  let h4 = Hashtbl.create 1 in 
  Hashtbl.add h4 [|true ; true ; true ; true|] 0 ;
  let h = Hashtbl.create 5 in 
  Hashtbl.add h 0 h0 ;
  Hashtbl.add h 1 h1 ;
  Hashtbl.add h 2 h2 ;
  Hashtbl.add h 3 h3 ;
  Hashtbl.add h 4 h4 ; 
  {n = 5 ; p = 4 ; init = 0 ; nb_final_sets = 2 ; term = [| [] ; [0] ; [0] ; [1] ; [1] |] ; delta = h}

let test_gba_to_ba () = (*succeeded - cf dossiertipe/sources/1er lien*)
  print_gba gba1 ;
  print_ba (gba_to_ba gba1) ;
  
  print_gba gba1bis ; 
  print_ba (gba_to_ba gba1bis)


let maxione a b c = not (a && b) && not (a && c) && not (b && c)
let is_accepted_by_rule t t' = (*règle en question : l'homme doit accompagner les animaux sur le bateau && un seul à la fois max*)
  if t.(0) = t'.(0) then t = t'
  else 
    let wolf = t.(0) = t.(1) && t.(1) <> t'.(1) in
    let sheep = t.(0) = t.(2) && t.(2) <> t'.(2) in 
    let cabbage = t.(0) = t.(3) && t.(3) <> t'.(3) in 
    maxione wolf sheep cabbage && (wolf || t.(1) = t'.(1)) && (sheep || t.(2) = t'.(2)) && (cabbage || t.(3) = t'.(3))

let m1:ks =
  let bin_to_bool b = if b = 0 then false else true in
  let lab1 = Array.make 16 [||] in
  for h = 0 to 1 do
    for w = 0 to 1 do
      for m = 0 to 1 do
        for c = 0 to 1 do
          lab1.(h*2*2*2 + w*2*2 + m*2 + c) <- [|bin_to_bool h ; bin_to_bool w ; bin_to_bool m ; bin_to_bool c|] 
        done
      done
    done
  done;
  let init1 = Array.make 16 false in 
  init1.(15) <- true ;
  let r1 = Array.make_matrix 16 16 false  in
  for i = 0 to 15 do
    for j = 0 to i do 
      if is_accepted_by_rule lab1.(i) lab1.(j) then (r1.(i).(j) <- true ; r1.(j).(i) <- true)
    done;
  done;
  {n = 16 ; p = 4 ; init = init1 ; r = r1 ; lab = lab1}

let test_ks_to_ba () = (*succeeded*)
  print_ks m1 ;
  print_ba (ks_to_ba m1) 

let test_language () = (*succeeded*)
  begin match language ba1 with
    |None -> printf "Language vide.\n"
    |Some lasso -> printf "lasso trouvé : " ; print_lasso lasso 
  end ; ()

(*//////////////// éxécution ////////////////*)

let main () = 
  test_language ()
  (*let f:formule = U (P 0 , P 1) in
  let f' = nnf f in 
  let pg = create_pre_graph f' in 
  print_pre_graph pg ; 
  let g = pre_graph_to_gba pg f' in 
  print_gba g ; 
  let g' = powerset g in 
  print_gba g' *)


let () = main ()