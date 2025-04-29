(* AST *)
type variable = { name : string; id : int }
[@@deriving show { with_path = false }]

type macro = { name : string; def : expression }
[@@deriving show { with_path = false }]

and expression =
  | Var of variable
  | Abs of variable * expression
  | App of expression * expression
  | Macro of macro
[@@deriving show { with_path = false }]

(* PRINT *)

let show_var_id = ref false
let show_delta_reduction = ref false
let lambda_stdout = ref ""
let lambda_stderr = ref ""

let print_expression e =
  let string_of_e = ref "" in
  let rec helper = function
    | Var v ->
        string_of_e :=
          !string_of_e ^ v.name
          ^ if !show_var_id then Int.to_string v.id else ""
    | Macro m -> string_of_e := !string_of_e ^ m.name
    | Abs (v, e) ->
        string_of_e :=
          !string_of_e ^ "(&lambda;"
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
  (* print_string !string_of_e; *)
  lambda_stdout := !lambda_stdout ^ !string_of_e

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
    let rec helper ?(previous_captured_var_id = -3)
        ?(previous_captured_again_var_id = -3) = function
      | Var v ->
          if v.id = -1 then
            string_of_e :=
              !string_of_e ^ !string_of_redex_abs ^ " " ^ !string_of_redex_app
          else
            string_of_e :=
              !string_of_e
              ^ (if
                   highlight_var_with_id = v.id
                   & v.id <> previous_captured_again_var_id
                 then highlight_color_start highlight_var_color
                 else "")
              ^ v.name
              ^ (if !show_var_id then Int.to_string v.id else "")
              ^
              if
                highlight_var_with_id = v.id
                & v.id <> previous_captured_again_var_id
              then highlight_color_end
              else ""
      | Macro m -> string_of_e := !string_of_e ^ m.name
      | Abs (v, e) ->
          string_of_e :=
            !string_of_e ^ "(&lambda;"
            ^ (if
                 highlight_var_with_id = v.id & v.id <> previous_captured_var_id
               then highlight_color_start highlight_var_color
               else "")
            ^ (v.name ^ if !show_var_id then Int.to_string v.id else "")
            ^ (if
                 highlight_var_with_id = v.id & v.id <> previous_captured_var_id
               then highlight_color_end
               else "")
            ^ ".";
          helper e
            ~previous_captured_var_id:
              (if highlight_var_with_id = v.id then v.id
               else previous_captured_var_id)
            ~previous_captured_again_var_id:
              (if v.id = previous_captured_var_id then v.id
               else previous_captured_again_var_id);
          string_of_e := !string_of_e ^ ")"
      | App (e1, e2) ->
          string_of_e := !string_of_e ^ "(";
          helper e1 ~previous_captured_var_id ~previous_captured_again_var_id;
          string_of_e := !string_of_e ^ " ";
          helper e2 ~previous_captured_var_id ~previous_captured_again_var_id;
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
  (* print_string !string_of_e; *)
  lambda_stdout := !lambda_stdout ^ !string_of_e

let print_highlighted_macro macro_of_e extension_of_macro_e =
  let highlight_macro_color = "#ff0" in
  let highlight_color_start c = "<span style=\"color:" ^ c ^ "\">" in
  let highlight_color_end = "</span>" in
  let string_of_macro = ref "" in
  let string_of_e = ref (highlight_color_start highlight_macro_color) in
  let rec helper = function
    | Var v ->
        if v.id = -1 then string_of_e := !string_of_e ^ !string_of_macro
        else
          string_of_e :=
            !string_of_e ^ v.name
            ^ if !show_var_id then Int.to_string v.id else ""
    | Macro m -> string_of_e := !string_of_e ^ m.name
    | Abs (v, e) ->
        string_of_e :=
          !string_of_e ^ "(&lambda;"
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
  helper macro_of_e;
  string_of_e := !string_of_e ^ highlight_color_end;
  string_of_macro := !string_of_e;
  string_of_e := "";
  helper (extension_of_macro_e (Var { name = ""; id = -1 }));
  (* print_string !string_of_e; *)
  lambda_stdout := !lambda_stdout ^ !string_of_e

let on_delta_reduction extension_of_e macro_of_e =
  print_highlighted_macro macro_of_e extension_of_e;
  (* print_string " --> \n"; *)
  lambda_stdout := !lambda_stdout ^ " == \n";
  (* print_endline "<br/>"; *)
  lambda_stdout := !lambda_stdout ^ "<br/>\n"

let on_reduction extension_of_e redex_of_e =
  print_highlighted_redex redex_of_e extension_of_e;
  (* print_string " --> \n"; *)
  lambda_stdout := !lambda_stdout ^ " --> \n";
  (* print_endline "<br/>"; *)
  lambda_stdout := !lambda_stdout ^ "<br/>\n"

(* PARSE *)
open Angstrom

let ws_newline =
  let is_ws = function
    | '\x20' | '\x0a' | '\x0d' | '\x09' -> true
    | _ -> false
  in
  take_while is_ws

let ws =
  let is_ws = function '\x20' | '\x0d' | '\x09' -> true | _ -> false in
  take_while is_ws

let token s = ws *> string s
let parens s = token "(" *> s <* token ")"

let chainl1 e op =
  let rec go acc = lift2 (fun f x -> f acc x) op e >>= go <|> return acc in
  e >>= fun init -> go init

let p_var =
  ws *> peek_char_fail >>= function
  | 'a' .. 'z' ->
      take_while1 (function 'a' .. 'z' | '0' .. '9' -> true | _ -> false)
  | _ -> fail ": Invalid variable definition"

let p_abs p_e =
  token "\\" *> p_var >>= fun v ->
  token "." *> p_e >>= fun e -> return (Abs ({ name = v; id = 0 }, e))

let p_app p_e = chainl1 p_e (return (fun e1 e2 -> App (e1, e2)))

let p_macro =
  lift2
    (fun name e_raw -> (name, e_raw))
    (ws
    *> take_while1 (function
         | 'A' .. 'Z' | '0' .. '9' | '_' -> true
         | _ -> false))
    (token "=" *> take_till (fun c -> c = '\n')
    <* ws <* token "\n" <* ws_newline)

let p_macro_name =
  ws *> peek_char_fail >>= function
  | 'A' .. 'Z' | '0' .. '9' | '_' ->
      take_while1 (function
        | 'A' .. 'Z' | '0' .. '9' | '_' -> true
        | _ -> false)
  | _ -> fail ": Invalid macro name"

module StringMap = Map.Make (String)

let p_expression macros =
  fix @@ fun p_expression ->
  let term =
    p_abs p_expression <|> parens p_expression
    <|> (p_var >>| fun v -> Var { name = v; id = 0 })
    <|> ( p_macro_name >>= fun m ->
          match StringMap.find_opt m macros with
          | Some m_def -> return (Macro { name = m; def = m_def })
          | None -> fail ": Unknown macro" )
  in
  let term = p_app term <|> term in
  term <* ws_newline

let p_program =
  ws_newline *> many p_macro
  >>= (fun raw_macros ->
        let macros = ref StringMap.empty in
        let is_fail = ref (false, "") in
        List.iter
          (* key - macro name, value - string of macro definition *)
            (fun (name, expr_raw) ->
            let macro_expr =
              match
                parse_string ~consume:All (p_expression !macros) expr_raw
              with
              | Ok e -> Some e
              | Error msg ->
                  if fst !is_fail then () else is_fail := (true, msg);
                  None
            in
            match macro_expr with
            | Some macro_expr -> macros := StringMap.add name macro_expr !macros
            | None -> ())
          raw_macros;
        (* last lambda expr *)
        if fst !is_fail then fail (snd !is_fail) else p_expression !macros)
  <* ws_newline

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
      | Macro m ->
          if !show_delta_reduction then
            Macro { name = m.name; def = helper env m.def }
          else helper env m.def
    in
    helper [] e
  in
  match parse_string ~consume:All p_program s with
  | Ok e -> annotate e
  | Error msg ->
      lambda_stderr := "Error" ^ msg;
      Var { name = ""; id = 0 }

(* REDUCE *)

type strategy = CBN | NO | CBV | AO

(* substitute x in e with the v *)
let rec subst e (x : variable) v =
  match e with
  | Var y -> if y.id = x.id then v else e
  | Abs (y, e1) -> if y.id = x.id then Abs (y, e1) else Abs (y, subst e1 x v)
  | App (e1, e2) -> App (subst e1 x v, subst e2 x v)
  | Macro m -> subst m.def x v

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
  | Macro m ->
      on_delta_reduction k (Macro { name = m.name; def = m.def });
      reduce_cbnk m.def k

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
  | Macro m ->
      on_delta_reduction k (Macro { name = m.name; def = m.def });
      reduce_cbvk m.def k

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
  | Macro m ->
      on_delta_reduction k (Macro { name = m.name; def = m.def });
      reduce_aok m.def k

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
  | Macro m ->
      on_delta_reduction k (Macro { name = m.name; def = m.def });
      reduce_nok m.def k

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

(* show_var_id, show_delta_reduction *)
let get_lambda__small_step ss s n svi sdr =
  lambda_stdout := "";
  show_var_id := svi;
  show_delta_reduction := sdr;
  print_expression (reduce ss n (parse_lambda s));
  if !lambda_stderr <> "" then (
    let res = !lambda_stderr in
    lambda_stderr := "";
    res)
  else !lambda_stdout

let run_lambda__small_step ss s n svi sdr =
  print_endline (get_lambda__small_step ss s n svi sdr)
