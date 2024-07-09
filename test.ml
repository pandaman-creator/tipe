open Printf



let main () = 
  let h = Hashtbl.create 5 in 
  Hashtbl.add h 2 3 ;
  Hashtbl.add h 2 4 ;
  let rec print_list = function
    |[] -> printf "[]" 
    |x::xs -> printf "%d\n" x ; print_list xs 
  in
  print_list (Hashtbl.find_all h 1) 


let () = main ()