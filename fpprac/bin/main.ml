open Lam

(* let () = run_lambda__small_step {|(\x. \y. x (\x. x y))y SUBS|} *)

(* cbv
   (\x. (a x) (b x)) ((\y. y) c)
*)
(* cbn
   (\x. x x) (\y. y y)
*)

(*f y f*)

let rec revk lst k =
  match lst with
  | [] -> k []
  | x :: xs -> revk xs (fun reversedlst -> k (reversedlst @ [ x ]))

let rec print_list = function
  | [] -> ()
  | x :: xs ->
      print_int x;
      print_endline "";
      print_list xs

let rec factk n k =
  if n <= 1 then k n
  else factk (n - 1) (fun fact_n_minus_one -> k (n * fact_n_minus_one))

let rec fibbk n k =
  if n <= 3 then k 1
  else
    fibbk (n - 1) (fun fibb_n_minus_one ->
        fibbk (n - 2) (fun fibb_n_minus_two ->
            k (fibb_n_minus_one + fibb_n_minus_two)))

let rec fold_leftk l f acc k =
  match l with [] -> k acc | hd :: tl -> fold_leftk tl f (f acc hd) k

let rec fold_rightk l f acc k =
  match l with
  | [] -> k acc
  | hd :: tl ->
      fold_rightk tl f acc (fun fold_right_acc -> k (f fold_right_acc hd))

(* Реализуйте функцию map для списков,
     которая получает список xs и функцию f,
     и применяет функцию к каждому элементу,
     и складывает в результат по порядку.
     Затем функцию map запишите в CPS.
     Учтите, что передаваемая функция f тоже может быть в
   CPS стиле.*)

(* let rec map xs f = match xs with [] -> [] | hd :: tl -> f hd :: map tl f
   (* let () = print_list (map [ 1; 2; 4 ] (fun x -> x * x)) *)

   let rec mapk xs f k =
     match xs with
     | [] -> k []
     | hd :: tl ->
         mapk tl f (fun mapped_tail ->
             k (f hd (fun hd_applied_cps -> hd_applied_cps :: mapped_tail))) *)

(* let () = mapk [ 5; 7; 10 ] (fun n -> fibbk n) print_list *)

(* Реализуйте функцию map для списков,
   которая получает список xs и функцию f,
   и применяет функцию к каждому элементу,
   и складывает в результат в ОБРАТНОМ порядке.
   Затем функцию map запишите в CPS.
   Учтите, что передаваемая функция f тоже может
   быть в CPS стиле*)

let rec map xs f = match xs with [] -> [] | hd :: tl -> map tl f @ [ f hd ]

let rec mapk xs f k =
  match xs with
  | [] -> k []
  | hd :: tl ->
      mapk tl f (fun mapped_reversed_tail ->
          k
            (f hd (fun applied_head_cps ->
                 mapped_reversed_tail @ [ applied_head_cps ])))

(* let () = mapk [ 5; 6; 7 ] factk print_list *)

let start k = k []
let push stack n k = k (n :: stack)

let add stack k =
  match stack with
  | a :: b :: rest -> k ((a + b) :: rest)
  | _ -> failwith "invalid stack configuration"

let fin stack =
  match stack with [ res ] -> print_int res | _ -> failwith "non empty stack"

(* let () = start push 1 push 3 add fin *)

type 'a t = Leaf of 'a * 'a * 'a | Node of ('a * 'a) t * ('a * 'a) t

let rec mapk : 'a 'b 'c. ('a -> 'b) -> 'a t -> ('b t -> 'c) -> 'c =
 fun f t k ->
  match t with
  | Leaf (l1, l2, l3) -> k (Leaf (f l1, f l2, f l3))
  | Node (t1, t2) ->
      let g (x, y) = (f x, f y) in
      mapk g t1 (fun mapped_t1 ->
          mapk g t2 (fun mapped_t2 -> k (Node (mapped_t1, mapped_t2))))

module MList = struct
  type 'a t = 'a list

  let return x = [ x ]

  let rec bindk x f k =
    match x with [] -> k [] | h :: t -> bindk t f (fun m -> k (f h :: m))
end

let rec bindk x f k =
  match x with [] -> k [] | h :: t -> bindk t f (fun m -> k (f h :: m))

let () = bindk [ 1; 2; 3 ] (fun x -> x * 2) print_list
