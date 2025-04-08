(* AST *)
type variable = { name : string; id : int }
[@@deriving show { with_path = false }]

type expression =
  | Var of variable
  | Abs of variable * expression
  | App of expression * expression
[@@deriving show { with_path = false }]

(* PRINT *)

let show_var_id = ref false

let print_expression e =
  let string_of_e = ref "" in
  let rec helper = function
    | Var v ->
        string_of_e :=
          !string_of_e ^ v.name
          ^ if !show_var_id then Int.to_string v.id else ""
    | Abs (v, e) ->
        string_of_e :=
          !string_of_e ^ "(λ"
          ^ (v.name ^ if !show_var_id then Int.to_string v.id else "")
          ^ ".";
        helper e;
        string_of_e := !string_of_e ^ ")"
    | App (e1, e2) ->
        string_of_e := !string_of_e ^ "(";
        helper e1;
        string_of_e := !string_of_e ^ " ";
        helper e2;
        string_of_e := !string_of_e ^ ")"
  in
  helper e;
  print_string !string_of_e

let print_highlighted_redex redex_of_e extension_of_redex_e =
  let abs_e, abs_x, app_e = redex_of_e in
  let highlight_expression_color = "#f00" in
  let highlight_var_color = "#00f" in
  let highlight_color_start c = "<span style=\"color:" ^ c ^ "\">" in
  let highlight_color_end = "</span>" in
  let string_of_redex_abs = ref "" in
  let string_of_redex_app = ref "" in
  let string_of_e = ref (highlight_color_start highlight_expression_color) in
  let get_string_of_e highlight_var_with_id =
    let rec helper = function
      | Var v ->
          if v.id = -1 then
            string_of_e :=
              !string_of_e ^ !string_of_redex_abs ^ " " ^ !string_of_redex_app
          else
            string_of_e :=
              !string_of_e
              ^ (if highlight_var_with_id = v.id then
                   highlight_color_start highlight_var_color
                 else "")
              ^ v.name
              ^ (if !show_var_id then Int.to_string v.id else "")
              ^ if highlight_var_with_id = v.id then highlight_color_end else ""
      | Abs (v, e) ->
          string_of_e :=
            !string_of_e ^ "(λ"
            ^ (if highlight_var_with_id = v.id then
                 highlight_color_start highlight_var_color
               else "")
            ^ (v.name ^ if !show_var_id then Int.to_string v.id else "")
            ^ (if highlight_var_with_id = v.id then highlight_color_end else "")
            ^ ".";
          helper e;
          string_of_e := !string_of_e ^ ")"
      | App (e1, e2) ->
          string_of_e := !string_of_e ^ "(";
          helper e1;
          string_of_e := !string_of_e ^ " ";
          helper e2;
          string_of_e := !string_of_e ^ ")"
    in
    helper
  in
  get_string_of_e (-2) app_e;
  string_of_e := !string_of_e ^ highlight_color_end;
  string_of_redex_app := !string_of_e;
  string_of_e := "";
  get_string_of_e abs_x.id (Abs (abs_x, abs_e));
  string_of_redex_abs := !string_of_e;
  string_of_e := "";
  let e_with_extension = extension_of_redex_e (Var { name = ""; id = -1 }) in
  get_string_of_e (-1) e_with_extension;
  print_string !string_of_e

let on_reduction extension_of_e redex_of_e =
  print_highlighted_redex redex_of_e extension_of_e;
  print_string " --> \n";
  print_endline "<br/>"

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

let p_var = ws *> take_while1 (function 'a' .. 'z' -> true | _ -> false)

let p_abs p_e =
  token "\\" *> p_var >>= fun v ->
  token "." *> p_e >>= fun e -> return (Abs ({ name = v; id = 0 }, e))

let p_app p_e = chainl1 p_e (return (fun e1 e2 -> App (e1, e2)))

let p_macro_def p_e =
  lift2
    (fun name e -> (name, e))
    (ws *> take_while1 (function 'A' .. 'Z' | '0' .. '9' -> true | _ -> false))
    (token "=" *> p_e <* token ";")

let p_macro =
  ws *> peek_char_fail >>= function
  | 'A' .. 'Z' | '0' .. '9' ->
      take_while1 (function 'A' .. 'Z' | '0' .. '9' -> true | _ -> false)
  | _ -> fail "not a macro"

module StringMap = Map.Make (String)

let p_expression macros =
  fix @@ fun p_expression ->
  let term =
    p_abs p_expression <|> parens p_expression
    <|> (p_var >>| fun v -> Var { name = v; id = 0 })
    <|> ( p_macro >>= fun m ->
          match StringMap.find_opt m macros with
          | Some e -> return e
          | None -> fail ("unknown macros, or in its definition: " ^ m) )
  in
  let term = p_app term <|> term in
  term

let p_program =
  let rec collect_macros macros =
    p_macro_def (p_expression macros)
    >>= (fun (name, expr) ->
          let macros = StringMap.add name expr macros in
          collect_macros macros)
    <|> return macros
  in
  collect_macros StringMap.empty >>= (fun macros -> p_expression macros) <* ws

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
  match parse_string ~consume:All p_program s with
  | Ok e -> annotate e
  | Error msg -> failwith ("Error: Parser. Check your lambda: " ^ msg)

(* REDUCE *)

type strategy = CBN | NO | CBV | AO

let rec subst e (x : variable) v =
  match e with
  | Var y -> if y.id = x.id then v else e
  | Abs (y, e1) -> if y.id = x.id then Abs (y, e1) else Abs (y, subst e1 x v)
  | App (e1, e2) -> App (subst e1 x v, subst e2 x v)

exception OneReduction of expression

(* rules: https://www.itu.dk/~sestoft/papers/sestoft-lamreduce.pdf *)

let rec reduce_cbnk current_e k =
  match current_e with
  | Var x -> Var x
  | Abs (x, e) -> Abs (x, e)
  | App (e1, e2) -> (
      match reduce_cbnk e1 (fun reduced_e1 -> k (App (reduced_e1, e2))) with
      | Abs (x, e) ->
          let s = subst e x e2 in
          on_reduction k (e, x, e2);
          raise (OneReduction (k s))
          (* reduce_cbnk s ... *)
          (* dont continue, stop after one redution *)
      | e1' -> App (e1', e2))

let reduce_cbn original_e =
  try
    let _ = reduce_cbnk original_e Fun.id in
    None
  with OneReduction next_e -> Some next_e

let rec reduce_cbvk current_e k =
  match current_e with
  | Var x -> Var x
  | Abs (x, e) -> Abs (x, e)
  | App (e1, e2) -> (
      match reduce_cbvk e1 (fun reduced_e1 -> k (App (reduced_e1, e2))) with
      | Abs (x, e) ->
          let e2' =
            reduce_cbvk e2 (fun reduced_e2 -> k (App (Abs (x, e), reduced_e2)))
          in
          let s = subst e x e2' in
          on_reduction k (e, x, e2');
          raise (OneReduction (k s))
          (* reduce_cbvk s ... *)
          (* dont continue, stop after one redution *)
      | e1' ->
          let e2' =
            reduce_cbvk e2 (fun reduced_e2 -> k (App (e1', reduced_e2)))
          in
          App (e1', e2'))

let reduce_cbv original_e =
  try
    let _ = reduce_cbvk original_e Fun.id in
    None
  with OneReduction next_e -> Some next_e

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
          on_reduction k (e, x, e2');
          raise (OneReduction (k s))
      (* reduce_aok s ... *)
      (* dont continue, stop after one redution *)
      | e1' ->
          let e2' =
            reduce_aok e2 (fun reduced_e2 -> k (App (e1', reduced_e2)))
          in
          App (e1', e2'))

let reduce_ao original_e =
  try
    let _ = reduce_aok original_e Fun.id in
    None
  with OneReduction next_e -> Some next_e

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
          on_reduction k (e, x, e2);
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

let reduce_no original_e =
  try
    let _ = reduce_nok original_e Fun.id in
    None
  with OneReduction next_e -> Some next_e

let rec loop_reduce reduction_function e n =
  if n <= 0 then e
  else
    match reduction_function e with
    | Some next_e -> loop_reduce reduction_function next_e (n - 1)
    | None -> e

let reduce (s : strategy) (n : int) (e : expression) =
  match s with
  | CBV -> loop_reduce reduce_cbv e n
  | CBN -> loop_reduce reduce_cbn e n
  | AO -> loop_reduce reduce_ao e n
  | NO -> loop_reduce reduce_no e n

(* RUNNING *)

let _ = show_var_id := false
let run_lambda s = print_expression (parse_lambda s)
let run_lambda__small_step s = print_expression (reduce NO 400 (parse_lambda s))
