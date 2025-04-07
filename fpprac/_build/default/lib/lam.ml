(* AST *)
type variable = { name : string; id : int }
[@@deriving show { with_path = false }]

type expression =
  | Var of variable
  | Abs of variable * expression
  | App of expression * expression
[@@deriving show { with_path = false }]

(* PRINT *)

let print_expression e =
  let rec helper = function
    | Var v -> print_string (v.name ^ Int.to_string v.id)
    (* | Var v -> print_string v.name *)
    | Abs (v, e) ->
        print_string ("(λ" ^ (v.name ^ Int.to_string v.id) ^ ".");
        (* print_string ("(λ" ^ v.name ^ "."); *)
        helper e;
        print_string ")"
    | App (e1, e2) ->
        print_string "(";
        helper e1;
        print_string " ";
        helper e2;
        print_string ")"
  in
  helper e;
  print_endline ""

(* PARSE *)
open Angstrom

let ws =
  let is_ws = function
    | '\x20' | '\x0a' | '\x0d' | '\x09' -> true
    | _ -> false
  in
  take_while is_ws

let token s = ws *> string s
let parens s = token "(" *> s <* token ")"

let chainl1 e op =
  let rec go acc = lift2 (fun f x -> f acc x) op e >>= go <|> return acc in
  e >>= fun init -> go init

let p_var =
  ws
  *> take_while1 (function
       | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' -> true
       | _ -> false)

let p_abs p_e =
  token "\\" *> p_var >>= fun v ->
  token "." *> p_e >>= fun e -> return (Abs ({ name = v; id = 0 }, e))

let p_app p_e = chainl1 p_e (return (fun e1 e2 -> App (e1, e2)))

let p_expression =
  ( fix @@ fun p_expression ->
    let term =
      p_abs p_expression <|> parens p_expression
      <|> (p_var >>| fun v -> Var { name = v; id = 0 })
    in
    let term = p_app term <|> term in
    term )
  <* ws

(* makes all variable unique by adding to each corresponding id. one way of implementing capture-avoiding substitution *)
let parse_lambda s =
  let annotate e =
    let fresh_id =
      let counter = ref 0 in
      fun () ->
        let id = !counter in
        counter := id + 1;
        id
    in
    let rec helper env = function
      | Var v -> (
          try
            let id = List.assoc v.name env in
            Var { name = v.name; id }
          with Not_found ->
            let id = fresh_id () in
            Var { name = v.name; id })
      | Abs (v, body) ->
          let new_id = fresh_id () in
          let v' = { name = v.name; id = new_id } in
          let env' = (v.name, new_id) :: env in
          Abs (v', helper env' body)
      | App (e1, e2) -> App (helper env e1, helper env e2)
    in
    helper [] e
  in
  match parse_string ~consume:All p_expression s with
  | Ok e -> annotate e
  | Error msg -> failwith ("Error: Parser. Check your lambda: " ^ msg)

(* REDUCE *)

type strategy = CBN | NO | CBV | AO

let rec subst e (x : variable) v =
  print_endline "Substitute:";
  print_expression v;
  print_endline ("for: " ^ (x.name ^ Int.to_string x.id) ^ " in:");
  print_expression e;
  print_endline "inside expression:";
  let rec helper e x v =
    match e with
    | Var y -> if y.id = x.id then v else e
    | Abs (y, e1) -> if y.id = x.id then Abs (y, e1) else Abs (y, helper e1 x v)
    | App (e1, e2) -> App (helper e1 x v, helper e2 x v)
  in
  helper e x v

exception OneReduction of expression

(* rules: https://www.itu.dk/~sestoft/papers/sestoft-lamreduce.pdf *)
let reduce_cbn original_e =
  let rec reduce_cbnk current_e k =
    match current_e with
    | Var x -> Var x
    | Abs (x, e) -> Abs (x, e)
    | App (e1, e2) -> (
        match reduce_cbnk e1 (fun reduced_e1 -> k (App (reduced_e1, e2))) with
        | Abs (x, e) ->
            let s = subst e x e2 in
            raise (OneReduction (k s))
            (* reduce_cbnk s ... *)
            (* dont continue, stop after one redution *)
        | e1' -> App (e1', e2))
  in
  try reduce_cbnk original_e Fun.id with OneReduction next_e -> next_e

let reduce_cbv original_e =
  let rec reduce_cbvk current_e k =
    match current_e with
    | Var x -> Var x
    | Abs (x, e) -> Abs (x, e)
    | App (e1, e2) -> (
        match reduce_cbvk e1 (fun reduced_e1 -> k (App (reduced_e1, e2))) with
        | Abs (x, e) ->
            let e2' =
              reduce_cbvk e2 (fun reduced_e2 ->
                  k (App (Abs (x, e), reduced_e2)))
            in
            let s = subst e x e2' in
            raise (OneReduction (k s))
            (* reduce_cbvk s ... *)
            (* dont continue, stop after one redution *)
        | e1' ->
            let e2' =
              reduce_cbvk e2 (fun reduced_e2 -> k (App (e1', reduced_e2)))
            in
            App (e1', e2'))
  in
  try reduce_cbvk original_e Fun.id with OneReduction next_e -> next_e

let reduce_ao original_e =
  let rec reduce_aok current_e k =
    match current_e with
    | Var x -> Var x
    | Abs (x, e) -> (
        match reduce_aok e (fun reduced_e -> k (Abs (x, reduced_e))) with
        | e' -> Abs (x, e'))
    | App (e1, e2) -> (
        match reduce_aok e1 (fun reduced_e1 -> k (App (reduced_e1, e2))) with
        | Abs (x, e) ->
            let e2' =
              reduce_aok e2 (fun reduced_e2 -> k (App (Abs (x, e), reduced_e2)))
            in
            let s = subst e x e2' in
            raise (OneReduction (k s))
        (* reduce_aok s *)
        (* dont continue, stop after one redution *)
        | e1' ->
            let e2' =
              reduce_aok e2 (fun reduced_e2 -> k (App (e1', reduced_e2)))
            in
            App (e1', e2'))
  in
  try reduce_aok original_e Fun.id with OneReduction next_e -> next_e

let reduce_no original_e =
  (* kopipasta start *)
  let rec reduce_cbnk current_e k =
    match current_e with
    | Var x -> Var x
    | Abs (x, e) -> Abs (x, e)
    | App (e1, e2) -> (
        match reduce_cbnk e1 (fun reduced_e1 -> k (App (reduced_e1, e2))) with
        | Abs (x, e) ->
            let s = subst e x e2 in
            raise (OneReduction (k s))
            (* reduce_cbnk s ... *)
            (* dont continue, stop after one redution *)
        | e1' -> App (e1', e2))
  in
  (* kopipasta end *)
  let rec reduce_nok current_e k =
    match current_e with
    | Var x -> Var x
    | Abs (x, e) -> (
        match reduce_nok e (fun reduced_e -> k (Abs (x, reduced_e))) with
        | e' -> Abs (x, e'))
    | App (e1, e2) -> (
        match reduce_cbnk e1 (fun reduced_e1 -> k (App (reduced_e1, e2))) with
        | Abs (x, e) ->
            let s = subst e x e2 in
            raise (OneReduction (k s))
        (* reduce_nok s *)
        (* dont continue, stop after one redution *)
        | e1' ->
            let e1'' =
              reduce_nok e1' (fun reduced_e1' -> k (App (reduced_e1', e2)))
            in
            let e2' =
              reduce_nok e2 (fun reduced_e2 -> k (App (e1'', reduced_e2)))
            in
            App (e1'', e2'))
  in
  try reduce_nok original_e Fun.id with OneReduction next_e -> next_e

let rec loop_reduce reduction_function e n =
  if n <= 0 then e
  else
    match reduction_function e with
    | next_e ->
        print_expression e;
        print_endline "";
        loop_reduce reduction_function next_e (n - 1)
(* | _ -> e *)

let reduce (s : strategy) (n : int) (e : expression) =
  match s with
  | CBV -> loop_reduce reduce_cbv e n
  | CBN -> loop_reduce reduce_cbn e n
  | AO -> loop_reduce reduce_ao e n
  | NO -> loop_reduce reduce_no e n

(* RUNNING *)

let run_lambda s = print_expression (parse_lambda s)
let run_lambda__small_step s = print_expression (reduce NO 10 (parse_lambda s))
