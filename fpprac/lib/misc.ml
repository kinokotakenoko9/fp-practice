(* parser *)

module Parser = struct
  type 'a parser =
    | Error
    | Ok of 'a * char list

  let return x s = Ok (x, s)

  let ( >>= ) p f s =
    match p s with
    | Error -> Error
    | Ok (h, t) -> f h t
  ;;
end

open Parser

let char c = function
  | h :: t when c = h -> return c t
  | _ -> Error
;;

let satisfy cond = function
  | h :: t when cond h -> return h t
  | _ -> Error
;;

let ( *> ) p1 p2 = p1 >>= fun _ -> p2
let ( <* ) p1 p2 = p1 >>= fun h -> p2 >>= fun _ -> return h

let many p =
  let rec helper s =
    match p s with
    | Error -> return [] s
    | Ok (h, t) -> (helper >>= fun xs -> return (h :: xs)) t
  in
  helper
;;

let rec gration n =
  if n <= 0 then (1.0 +. sqrt 5.0) /. 2.0 else 1.0 /. (gration (n - 1) -. 1.0)
;;

let rec summing n total = if n = 0 then total else summing (n - 1) (n + total)

(* let () = print_int (summing 20 0) *)
let rec powerk n p acc = if p = 0 then acc else powerk n (p - 1) (acc * n)
(* let () = print_int (powerk 3 7 1) *)
