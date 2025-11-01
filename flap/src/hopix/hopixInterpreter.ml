open Position
open Error
open HopixAST

(** [error pos msg] reports execution error messages. *)
let error positions msg =
  errorN "execution" positions msg

(** Every expression of Hopix evaluates into a [value].

   The [value] type is not defined here. Instead, it will be defined
   by instantiation of following ['e gvalue] with ['e = environment].
   Why? The value type and the environment type are mutually recursive
   and since we do not want to define them simultaneously, this
   parameterization is a way to describe how the value type will use
   the environment type without an actual definition of this type.

*)
type 'e gvalue =
  | VInt       of Mint.t
  | VChar      of char
  | VString    of string
  | VUnit
  | VTagged    of constructor * 'e gvalue list
  | VTuple     of 'e gvalue list
  | VRecord    of (label * 'e gvalue) list
  | VLocation  of Memory.location
  | VClosure   of 'e * pattern located * expression located
  | VPrimitive of string * ('e gvalue Memory.t -> 'e gvalue -> 'e gvalue)

(** Two values for booleans. *)
let ptrue  = VTagged (KId "True", [])
let pfalse = VTagged (KId "False", [])

(**
    We often need to check that a value has a specific shape.
    To that end, we introduce the following coercions. A
    coercion of type [('a, 'e)] coercion tries to convert an
    Hopix value into a OCaml value of type ['a]. If this conversion
    fails, it returns [None].
*)

type ('a, 'e) coercion = 'e gvalue -> 'a option
let fail = None
let ret x = Some x
let value_as_int      = function VInt x -> ret x | _ -> fail
let value_as_char     = function VChar c -> ret c | _ -> fail
let value_as_string   = function VString s -> ret s | _ -> fail
let value_as_tagged   = function VTagged (k, vs) -> ret (k, vs) | _ -> fail
let value_as_record   = function VRecord fs -> ret fs | _ -> fail
let value_as_location = function VLocation l -> ret l | _ -> fail
let value_as_closure  = function VClosure (e, p, b) -> ret (e, p, b) | _ -> fail
let value_as_primitive = function VPrimitive (p, f) -> ret (p, f) | _ -> fail
let value_as_bool = function
  | VTagged (KId "True", []) -> true
  | VTagged (KId "False", []) -> false
  | _ -> assert false

(**
   It is also very common to have to inject an OCaml value into
   the types of Hopix values. That is the purpose of a wrapper.
 *)
type ('a, 'e) wrapper = 'a -> 'e gvalue
let int_as_value x  = VInt x
let bool_as_value b = if b then ptrue else pfalse

(**

  The flap toplevel needs to print the result of evaluations. This is
   especially useful for debugging and testing purpose. Do not modify
   the code of this function since it is used by the testsuite.

*)
let print_value m v =
  (** To avoid to print large (or infinite) values, we stop at depth 5. *)
  let max_depth = 5 in

  let rec print_value d v =
    if d >= max_depth then "..." else
      match v with
        | VInt x ->
          Mint.to_string x
        | VChar c ->
          "'" ^ Char.escaped c ^ "'"
        | VString s ->
          "\"" ^ String.escaped s ^ "\""
        | VUnit ->
          "()"
        | VLocation a ->
          print_array_value d (Memory.dereference m a)
        | VTagged (KId k, []) ->
          k
        | VTagged (KId k, vs) ->
          k ^ print_tuple d vs
        | VTuple (vs) ->
           print_tuple d vs
        | VRecord fs ->
           "{"
           ^ String.concat ", " (
                 List.map (fun (LId f, v) -> f ^ " = " ^ print_value (d + 1) v
           ) fs) ^ "}"
        | VClosure _ ->
          "<fun>"
        | VPrimitive (s, _) ->
          Printf.sprintf "<primitive: %s>" s
    and print_tuple d vs =
      "(" ^ String.concat ", " (List.map (print_value (d + 1)) vs) ^ ")"
    and print_array_value d block =
      let r = Memory.read block in
      let n = Mint.to_int (Memory.size block) in
      "[ " ^ String.concat ", " (
                 List.(map (fun i -> print_value (d + 1) (r (Mint.of_int i)))
                         (ExtStd.List.range 0 (n - 1))
               )) ^ " ]"
  in
  print_value 0 v

let print_values m vs =
  String.concat "; " (List.map (print_value m) vs)

module Environment : sig
  (** Evaluation environments map identifiers to values. *)
  type t

  (** The empty environment. *)
  val empty : t

  (** [bind env x v] extends [env] with a binding from [x] to [v]. *)
  val bind    : t -> identifier -> t gvalue -> t

  (** [update pos x env v] modifies the binding of [x] in [env] so
      that [x ↦ v] ∈ [env]. *)
  val update  : Position.t -> identifier -> t -> t gvalue -> unit

  (** [lookup pos x env] returns [v] such that [x ↦ v] ∈ env. *)
  val lookup  : Position.t -> identifier -> t -> t gvalue

  (** [UnboundIdentifier (x, pos)] is raised when [update] or
      [lookup] assume that there is a binding for [x] in [env],
      where there is no such binding. *)
  exception UnboundIdentifier of identifier * Position.t

  (** [last env] returns the latest binding in [env] if it exists. *)
  val last    : t -> (identifier * t gvalue * t) option

  (** [print env] returns a human readable representation of [env]. *)
  val print   : t gvalue Memory.t -> t -> string
end = struct

  type t =
    | EEmpty
    | EBind of identifier * t gvalue ref * t

  let empty = EEmpty

  let bind e x v =
    EBind (x, ref v, e)

  exception UnboundIdentifier of identifier * Position.t

  let lookup' pos x =
    let rec aux = function
      | EEmpty -> raise (UnboundIdentifier (x, pos))
      | EBind (y, v, e) ->
        if x = y then v else aux e
    in
    aux

  let lookup pos x e = !(lookup' pos x e)

  let update pos x e v =
    lookup' pos x e := v

  let last = function
    | EBind (x, v, e) -> Some (x, !v, e)
    | EEmpty -> None

  let print_binding m (Id x, v) =
    x ^ " = " ^ print_value m !v

  let print m e =
    let b = Buffer.create 13 in
    let push x v = Buffer.add_string b (print_binding m (x, v)) in
    let rec aux = function
      | EEmpty -> Buffer.contents b
      | EBind (x, v, EEmpty) -> push x v; aux EEmpty
      | EBind (x, v, e) -> push x v; Buffer.add_string b "\n"; aux e
    in
    aux e

end

(**
    We have everything we need now to define [value] as an instantiation
    of ['e gvalue] with ['e = Environment.t], as promised.
*)
type value = Environment.t gvalue

(**
   The following higher-order function lifts a function [f] of type
   ['a -> 'b] as a [name]d Hopix primitive function, that is, an
   OCaml function of type [value -> value].
*)
let primitive name ?(error = fun () -> assert false) coercion wrapper f
: value
= VPrimitive (name, fun x ->
    match coercion x with
      | None -> error ()
      | Some x -> wrapper (f x)
  )

type runtime = {
  memory      : value Memory.t;
  environment : Environment.t;
}

type observable = {
  new_memory      : value Memory.t;
  new_environment : Environment.t;
}

(** [primitives] is an environment that contains the implementation
    of all primitives (+, <, ...). *)
let primitives =
  let intbin name out op =
    let error m v =
      Printf.eprintf
        "Invalid arguments for `%s': %s\n"
        name (print_value m v);
      assert false (* By typing. *)
    in
    VPrimitive (name, fun m -> function
      | VInt x ->
         VPrimitive (name, fun m -> function
         | VInt y -> out (op x y)
         | v -> error m v)
      | v -> error m v)
  in
  let bind_all what l x =
    List.fold_left (fun env (x, v) -> Environment.bind env (Id x) (what x v))
      x l
  in
  (* Define arithmetic binary operators. *)
  let binarith name =
    intbin name (fun x -> VInt x) in
  let binarithops = Mint.(
    [ ("`+`", add); ("`-`", sub); ("`*`", mul); ("`/`", div) ]
  ) in
  (* Define arithmetic comparison operators. *)
  let cmparith name = intbin name bool_as_value in
  let cmparithops =
    [ ("`=?`", ( = ));
      ("`<?`", ( < ));
      ("`>?`", ( > ));
      ("`>=?`", ( >= ));
      ("`<=?`", ( <= )) ]
  in
  let boolbin name out op =
    VPrimitive (name, fun _ x -> VPrimitive (name, fun _ y ->
        out (op (value_as_bool x) (value_as_bool y))))
  in
  let boolarith name = boolbin name (fun x -> if x then ptrue else pfalse) in
  let boolarithops =
    [ ("`||`", ( || )); ("`&&`", ( && )) ]
  in
  let generic_printer =
    VPrimitive ("print", fun m v ->
      output_string stdout (print_value m v);
      flush stdout;
      VUnit
    )
  in
  let print s =
    output_string stdout s;
    flush stdout;
    VUnit
  in
  let print_int =
    VPrimitive  ("print_int", fun _ -> function
      | VInt x -> print (Mint.to_string x)
      | _ -> assert false (* By typing. *)
    )
  in
  let print_string =
    VPrimitive  ("print_string", fun _ -> function
      | VString x -> print x
      | _ -> assert false (* By typing. *)
    )
  in
  let bind' x w env = Environment.bind env (Id x) w in
  Environment.empty
  |> bind_all binarith binarithops
  |> bind_all cmparith cmparithops
  |> bind_all boolarith boolarithops
  |> bind' "print"        generic_printer
  |> bind' "print_int"    print_int
  |> bind' "print_string" print_string
  |> bind' "true"         ptrue
  |> bind' "false"        pfalse
  |> bind' "nothing"      VUnit
  
  let initial_runtime () = {
    memory      = Memory.create (640 * 1024 (* should be enough. -- B.Gates *));
    environment = primitives;
    }
    
exception PatternMatchFailure of Position.t
let rec evaluate runtime ast =
  try
    let runtime' = List.fold_left definition runtime ast in
    (runtime', extract_observable runtime runtime')
  with Environment.UnboundIdentifier (Id x, pos) ->
    Error.error "interpretation" pos (Printf.sprintf "`%s' is unbound." x)

(** [definition pos runtime d] evaluates the new definition [d]
    into a new runtime [runtime']. In the specification, this
    is the judgment:

                        E, M ⊢ dv ⇒ E', M'

*)

and definition runtime d =
  match Position.value d with 
  | DefineValue vd -> value_definition runtime vd
  (* We ignore Type definition *)
  | _ -> runtime





and value_definition runtime vd =
  match vd with
  | SimpleValue (id,_,e) ->
    let id = Position.value id in
    let new_env = Environment.bind runtime.environment id (expression' runtime.environment runtime.memory e) in
    { runtime with environment = new_env }
  | RecFunctions fdefs ->
    {runtime with environment = rec_functions runtime.environment runtime.memory fdefs}




and function_definition environment (FunctionDefinition (pat, body)) =
  VClosure (environment, pat, body)



and rec_functions environment memory = function 
    | [] -> environment
    | (id,_,fd):: fdefs ->
      (* We create a closure for the FunctionDefinition *)
      let closure = function_definition environment fd in
      let new_env = Environment.bind environment (Position.value id) closure in
      (* We continue with the rest of the list of function *)
      rec_functions new_env memory fdefs


and expression' environment memory e =
  expression (position e) environment memory (value e)

(** [expression pos runtime e] evaluates into a value [v] if

                          E, M ⊢ e ⇓ v, M'

   and E = [runtime.environment], M = [runtime.memory].
*)
and expression pos environment memory = 
  function 
  | Literal e ->  eval_literal e
  | Apply (e1,e2) -> 
    apply_expr e1 e2 environment memory pos
  | Variable (id, _) ->
    Environment.lookup pos (Position.value id) environment 
  | Tagged (cons, _ , expr) -> 
    let vlist = List.map (expression' environment memory) expr in
    VTagged (Position.value cons, vlist)
  | Record (fields, _ ) -> 
    let vfields = List.map (fun (label, expr) ->
      (Position.value label, expression' environment memory expr)
    ) fields in
    VRecord vfields
  | Field (expr, label, tys) -> error [pos] "Field evaluation not implemented yet"
  | Tuple expr -> 
    let vlist = List.map (expression' environment memory) expr in
    VTuple vlist
  | Sequence seq -> sequence environment memory seq
  | Define (def, expr) -> 
    let new_runtime = value_definition {memory; environment} def in
    expression' new_runtime.environment new_runtime.memory expr
  | Fun _ -> error [pos] "Function evaluation not implemented yet"
  | Ref expr -> reference environment memory expr 
  | Assign (name, value) -> assign environment memory (name,value) pos 
  | Read expr -> read environment memory expr pos 
  | Case (e, branchs) -> case environment memory (e,branchs) pos
  | IfThenElse (cond, then_e, else_e) -> if_then_else environment memory (cond, then_e, else_e)
  | While (cond, body) -> while_loop environment memory (cond,body) pos
  | For (id,lower,upper,body)-> for_loop environment memory (id,lower,upper,body) pos 
  | TypeAnnotation _ -> error [pos] "Type Annotation evaluation not implemented yet"


and eval_literal e =
  match Position.value e with
  | LInt i -> VInt i
  | LString s -> VString s 
  | LChar c -> VChar c


  
and apply_expr f x environment memory pos =
  let vx = expression' environment memory x in
  let vf = expression' environment memory f in
  match vf with 
  (* Primitive function already implemented in OCaml*)
  | VPrimitive (_,func) -> func memory vx
  | VClosure (env, p, body) ->
    let new_env = 
      try 
        (* We check if the function's pattern matches the argument value *)
        pattern' p env vx 
    with PatternMatchFailure pos ->
      error [pos] "Pattern match failure in function application."
    in
    (* We evaluate the body with the new environment where the pattern variables are bound *)
    expression' new_env memory body
    
    | _ -> error [pos] "Trying to apply a non-function value."
   
and sequence environment memory exprs = 
  match exprs with
  | [] -> VUnit
  | [e] -> expression' environment memory e
  | e :: t -> 
    let _ = expression' environment memory e in
    sequence environment memory t


and reference environment memory expr =
  let v = expression' environment memory expr in
  (*? we allocate one ?*)
  let location = Memory.allocate memory Mint.one v in
  VLocation location

and assign environment memory (name, value) pos =
  let vname = expression' environment memory name in 
  match  value_as_location vname  with
  | None -> error [pos] "Trying to assign a non-location value."
  | Some loc -> 
    let new_value = expression' environment memory value in
    Memory.write (Memory.dereference memory loc) Mint.zero new_value;
    VUnit 




  
and read environment memory expr pos =
  let v = expression' environment memory expr in
  match value_as_location v with 
  | None -> error [pos] "Trying to dereference a non-location value."
  | Some loc -> let loc = Memory.dereference memory loc in Memory.read loc Mint.zero
 
  

and case environment memory (e,branches) pos = 
  let ve = expression' environment memory e in
  match branches with
  | [] ->  error [pos] "Non exhaustive pattern match."
  | pats ->
    let rec aux = function 
    | [] -> error [pos] "Non exhaustive pattern match."
    | p :: t ->
      let Branch (pat, expr) = Position.value p in
      try 
        let new_env = pattern' pat environment ve in  
        expression' new_env memory expr
      with PatternMatchFailure _ -> aux t
    in aux pats




and if_then_else  environment memory (cond, then_e, else_e) = 
  let vcond = expression' environment memory cond in 
  match value_as_bool vcond with 
  | true -> expression' environment memory then_e
  | false -> expression' environment memory else_e



and while_loop environment memory (cond,body) pos =
  let rec aux memory =
    let vcond = expression' environment memory cond in 
    match value_as_bool vcond with 
    | true ->
      begin
      let body_value = expression' environment memory body in
      match body_value with
      | VUnit -> aux memory
      | _ -> error [pos] "This expression should return unit."
      end
    | false -> VUnit

    in aux memory


and for_loop environment memory (id,lower,upper,body) pos =
  let vlower = expression' environment memory lower in
  let vupper = expression' environment memory upper in
  match value_as_int vlower, value_as_int vupper with
  | Some l, Some u ->
    let rec aux i environment memory =
      if Mint.to_int i > Mint.to_int u then VUnit
      else 
        let new_env = Environment.bind environment (Position.value id) (VInt i) in
        let body_value = expression' new_env memory body in
        match body_value with
        | VUnit -> aux (Mint.add i Mint.one) environment memory
        | _ -> error [pos] "This expression should return unit."
    in aux l environment memory
  | _ -> error [pos] "Bounds of for loop should be integers."


and pattern' pat environment vx = 
  pattern (position pat) environment vx (value pat)
        
(** [pattern pos env value pat] extends [env] so that [value] is captured by [pat], and raises an exception otherwise. :

            env ⊢ value ∼ pat ⇝ env'

*)

        
and pattern pos environment value pat = 
  match pat with 
  | PVariable id -> pattern_variable id environment value 
  | PWildcard -> environment 
  | PTypeAnnotation (p, _) -> pattern' p environment value
  | PLiteral l ->  
    (* if it's a literal we just need to compare both values *)
    let literal_value = eval_literal l  in
      if literal_value = value then environment 
      else raise (PatternMatchFailure pos)
 
  | PTaggedValue (constr, tys, pats) -> tagged_pattern pos environment value (constr, tys, pats) 
  | PRecord (fs, _) -> record_pattern pos environment value fs 
  | PTuple ps -> tuple pos environment value ps 
  | POr pats -> pattern_or pos environment value pats
  | PAnd pats  -> pattern_and pos environment value pats

and pattern_list environment values pats = 
  List.fold_left2 (fun env v p -> pattern' p env v) environment values pats


and pattern_variable id environment value = 
  let id  = Position.value id in 
  Environment.bind environment id value 


and tagged_pattern pos environment value (constr, _, pats) =
  match value_as_tagged value with
  | None -> raise (PatternMatchFailure pos)
  | Some (k, vs) -> 
    if k <> constr.value then raise (PatternMatchFailure pos);
    pattern_list environment vs pats


and record_pattern pos environment value fs = 
  match value_as_record value with 
  | None -> raise (PatternMatchFailure pos )
  | Some fields ->
     let rec aux fields pats environment = 
      match fields,pats with 
      | _, [] -> environment
      | [], _ -> raise (PatternMatchFailure pos)
      | (l1, v) :: tfields, (l2, p) :: tpats ->
        if l1 <> Position.value l2 then raise (PatternMatchFailure pos);
        let new_env = pattern' p environment v in
        aux tfields tpats new_env
     in
     aux fields fs environment

and tuple pos environment value pats = 
  match value with 
  | VTuple values -> 
    if List.length values <> List.length pats then raise (PatternMatchFailure pos);
    pattern_list environment values pats
  | _ -> raise (PatternMatchFailure pos)

and pattern_or pos environment value pats = match pats with 
  | [] -> raise (PatternMatchFailure pos)
  | p :: t ->
    try 
      pattern' p environment value
      (* If the first pattern fail we try the next one because it's an "or" *)
    with PatternMatchFailure _ -> pattern_or pos environment value t


and pattern_and pos environment value pats = match pats with 
  |[] -> environment 
  | p :: t ->
    try 
      pattern' p environment value
    (* If one pattern fail we raise the exception because it's an "and" *)
    with PatternMatchFailure _ -> raise (PatternMatchFailure pos)
    (* If it succeed we give the new environment to the next pattern *)
    |> fun env' -> pattern_and pos env' value t


(** This function returns the difference between two runtimes. *)
and extract_observable runtime runtime' =
  let rec substract new_environment env env' =
    if env == env' then new_environment
    else
      match Environment.last env' with
        | None -> assert false (* Absurd. *)
        | Some (x, v, env') ->
          let new_environment = Environment.bind new_environment x v in
          substract new_environment env env'
  in
  {
    new_environment =
      substract Environment.empty runtime.environment runtime'.environment;
    new_memory =
      runtime'.memory
  }

(** This function displays a difference between two runtimes. *)
let print_observable (_ : runtime) observation =
  Environment.print observation.new_memory observation.new_environment
