(** This module implements a compiler from Hobix to Fopix. *)

(** As in any module that implements {!Compilers.Compiler}, the source
    language and the target language must be specified. *)

module Source = Hobix
module S = Source.AST
module Target = Fopix
module T = Target.AST

(**

   The translation from Hobix to Fopix turns anonymous
   lambda-abstractions into toplevel functions and applications into
   function calls. In other words, it translates a high-level language
   (like OCaml) into a first order language (like C).

   To do so, we follow the closure conversion technique.

   The idea is to make explicit the construction of closures, which
   represent functions as first-class objects. A closure is a block
   that contains a code pointer to a toplevel function [f] followed by all
   the values needed to execute the body of [f]. For instance, consider
   the following OCaml code:

   let f =
     let x = 6 * 7 in
     let z = x + 1 in
     fun y -> x + y * z

   The values needed to execute the function "fun y -> x + y * z" are
   its free variables "x" and "z". The same program with explicit usage
   of closure can be written like this:

   let g y env = env[1] + y * env[2]
   let f =
      let x = 6 * 7 in
      let z = x + 1 in
      [| g; x; z |]

   (in an imaginary OCaml in which arrays are untyped.)

   Once closures are explicited, there are no more anonymous functions!

   But, wait, how to we call such a function? Let us see that on an
   example:

   let f = ... (* As in the previous example *)
   let u = f 0

   The application "f 0" must be turned into an expression in which
   "f" is a closure and the call to "f" is replaced to a call to "g"
   with the proper arguments. The argument "y" of "g" is known from
   the application: it is "0". Now, where is "env"? Easy! It is the
   closure itself! We get:

   let g y env = env[1] + y * env[2]
   let f =
      let x = 6 * 7 in
      let z = x + 1 in
      [| g; x; z |]
   let u = f[0] 0 f

   (Remark: Did you notice that this form of "auto-application" is
   very similar to the way "this" is defined in object-oriented
   programming languages?)

*)

(**
   Helpers functions.
*)

let error pos msg =
  Error.error "compilation" pos msg

let make_fresh_variable =
  let r = ref 0 in
  fun () -> incr r; T.Id (Printf.sprintf "_%d" !r)


let make_fresh_function_identifier =
  let r = ref 0 in
  fun () -> incr r; T.FunId (Printf.sprintf "_%d" !r)

let define e f =
  let x = make_fresh_variable () in
  T.Define (x, e, f x)

let rec defines ds e =
  match ds with
    | [] ->
      e
    | (x, d) :: ds ->
      T.Define (x, d, defines ds e)

let seq a b =
  define a (fun _ -> b)

let rec seqs = function
  | [] -> assert false
  | [x] -> x
  | x :: xs -> seq x (seqs xs)

let allocate_block e =
  T.(FunCall (FunId "allocate_block", [e]))

let write_block e i v =
  T.(FunCall (FunId "write_block", [e; i; v]))

let read_block e i =
  T.(FunCall (FunId "read_block", [e; i]))

let lint i =
  T.(Literal (LInt (Int64.of_int i)))


(** [free_variables e] returns the list of free variables that
     occur in [e].*)
let free_variables =
  let module M =
    Set.Make (struct type t = S.identifier let compare = compare end)
  in
  let rec unions f = function
    | [] -> M.empty
    | [s] -> f s
    | s :: xs -> M.union (f s) (unions f xs)
  in
  let rec fvs = function
    | S.Literal _ ->
       M.empty
    | S.Variable x ->
       M.singleton x
    | S.While (cond, e) ->
      let f_cond = fvs cond in 
      let f_body = fvs e in 
      M.union f_body f_cond 
    | S.Define (vd, a) ->
      begin
        match vd with 
        | SimpleValue (id, e) -> 
          let f_e = fvs e in
          M.union f_e (M.diff (fvs a) (M.singleton id))
        | RecFunctions fdefs ->
          (* Get recursives func id *)
          let fs_ids = List.map (fun (id, _) -> id) fdefs in
          let fs_set = M.of_list fs_ids in
          
          (* Calculate defines free variables *)
          let defs_fvs = unions (fun (_, e) -> fvs e) fdefs in
          
          (* Calculate body free variables *)
          let body_fvs = fvs a in
          
          (* Everything without func ids *)
          M.diff (M.union defs_fvs body_fvs) fs_set
      end
    | S.ReadBlock (a, b) ->
       unions fvs [a; b]
    | S.Apply (a, b) ->
       unions fvs (a :: b)
    | S.WriteBlock (a, b, c) | S.IfThenElse (a, b, c) ->
       unions fvs [a; b; c]
    | S.AllocateBlock a ->
       fvs a
    | S.Fun (xs, e) ->
        M.diff (fvs e) (unions (fun x -> M.singleton x) xs)
    | S.Switch (a, b, c) ->
       let c = match c with None -> [] | Some c -> [c] in
       unions fvs (a :: ExtStd.Array.present_to_list b @ c)
  in
  fun e -> M.elements (fvs e)

(**

    A closure compilation environment relates an identifier to the way
    it is accessed in the compiled version of the function's
    body.

    Indeed, consider the following example. Imagine that the following
    function is to be compiled:

    fun x -> x + y

    In that case, the closure compilation environment will contain:

    x -> x
    y -> "the code that extract the value of y from the closure environment"

    Indeed, "x" is a local variable that can be accessed directly in
    the compiled version of this function's body whereas "y" is a free
    variable whose value must be retrieved from the closure's
    environment.

*)
type environment = {
    vars : (HobixAST.identifier, FopixAST.expression) Dict.t;
    externals : (HobixAST.identifier, int) Dict.t;
}

let primitives = [
    ("print_int", 1);
    ("print_string", 1);
    ("print", 1);
    ("true", 0); ("false", 0); ("nothing", 0);
    ("`+`", 2); ("`-`", 2); ("`*`", 2); ("`/`", 2);
    ("`||`", 2); ("`&&`", 2); 
    ("`=?`", 2); ("`<=?`", 2); ("`>=?`", 2); ("`<?`", 2); ("`>?`", 2);
]

let initial_environment () =
  let externals = List.fold_left 
    (fun dict (name, arity) -> Dict.insert (S.Id name) arity dict) 
    Dict.empty 
    primitives 
  in
  { vars = Dict.empty; externals = externals }

let bind_external id n env =
  { env with externals = Dict.insert id n env.externals }

let is_external id env =
  Dict.lookup id env.externals <> None

let reset_vars env =
   { env with vars = Dict.empty }

(** Precondition: [is_external id env = true]. *)
let arity_of_external id env =
  match Dict.lookup id env.externals with
    | Some n -> n
    | None -> assert false (* By is_external. *)


(** [translate p env] turns an Hobix program [p] into a Fopix program
    using [env] to retrieve contextual information. *)
let translate (p : S.t) env =
  let standard_library_defs = 
    List.map (fun (name, arity) -> 
      T.ExternalFunction (T.FunId name, arity)
    ) primitives 
  in

  let rec program env defs =
    let env, defs = ExtStd.List.foldmap definition env defs in
    (standard_library_defs @ List.flatten defs, env)
  and definition env = function
    | S.DeclareExtern (id, n) ->
       let env = bind_external id n env in
       (env, [T.ExternalFunction (function_identifier id, n)])
    | S.DefineValue vd ->
       (env, value_definition env vd)
  and value_definition env = function
    | S.SimpleValue (x, e) ->
       let fs, e = expression (reset_vars env) e in
       fs @ [T.DefineValue (identifier x, e)]
    | S.RecFunctions fdefs ->
      (* env to define_recursive_functions to see if there is externals*)
      let fs, defs = define_recursive_functions env fdefs in
      fs @ List.map (fun (x, e) -> T.DefineValue (x, e)) defs

  and define_recursive_functions env fdefs =
    let (global_funs, allocs, inits) = compile_recursive_group env fdefs in
    
    (* allocations : val ptr_f = allocate(...) *)
    let defs_allocs = List.map (fun (ptr, alloc_expr) -> 
      T.DefineValue (ptr, alloc_expr)
    ) allocs in

    (* init : val _ = (write... ; write...) *)
    let def_writes = 
      if inits = [] then [] 
      else [T.DefineValue (make_fresh_variable (), seqs inits)] 
    in
    
    (* Combine func code, allocations, and inits *)
    let fs = global_funs @ defs_allocs @ def_writes in

    (* Binding : defs list *)
    let defs = List.map2 (fun (id, _) (ptr, _) ->
      (identifier id, T.Variable ptr)
    ) fdefs allocs in

    (fs, defs)
  and expression env = function
    | S.Literal l ->
      [], T.Literal (literal l)
    | S.While (cond, e) ->
       let cfs, cond = expression env cond in
       let efs, e = expression env e in
       cfs @ efs, T.While (cond, e)
    | S.Variable x ->
      let xc =
        match Dict.lookup x env.vars with
          | Some e -> e (* Local Var *)
          | None -> 
              if is_external x env then
                (* Primitive *)
                T.Literal (T.LFun (function_identifier x))
              else
                (* Global Var *)
                T.Variable (identifier x)
      in
      ([], xc)
    | S.Define (vdef, a) ->
      begin
        match vdef with
        | SimpleValue (id,e) -> 
          let t_id  = identifier id in 
          let efs, e = expression env e in 
          
          (* Add id to env*)
          let env_body = { env with vars = Dict.insert id (T.Variable t_id) env.vars } in

          (* use the new env to *)
          let efs', e' = expression env_body a in 
          efs @ efs',T.Define (t_id, e,e')

        | RecFunctions fdefs ->
          (* compile rec func *)
          let (global_funs, allocs, inits) = compile_recursive_group env fdefs in
          
          (* Rebuild env_body : ptrs and ids in the order *)
          let ptrs = List.map fst allocs in
          let ids = List.map (fun (id, _) -> id) fdefs in
          let env_body = List.fold_left2 (fun e id ptr -> 
              { e with vars = Dict.insert id (T.Variable ptr) e.vars }
          ) env ids ptrs in

          (* compile a with new env *)
          let afs, expr_a = expression env_body a in

          (* Assemble : Alloc -> ... -> Alloc -> Init -> ... -> Init -> A *)
          let body_with_inits = 
            if inits = [] then expr_a
            else seq (seqs inits) expr_a
          in
          
          (* Wrap every ptr with T.Define *)
          let expr_final = List.fold_right (fun (ptr, alloc_expr) acc ->
            T.Define (ptr, alloc_expr, acc)
          ) allocs body_with_inits in
          
          (global_funs @ afs, expr_final)


      end



    | S.Apply (a, bs) ->
      (* Check if a is a primitive *)
      let is_primitive = match a with
        | S.Variable id -> is_external id env
        | _ -> false
      in

      if is_primitive then
        (* Extract id *)
        let id = match a with 
        | S.Variable x -> x 
        | _ -> assert false in

        (* Compile args *)
        let bfs, bs_exprs = expressions env bs in

        (* Function call with primitive *)
        (bfs, T.FunCall (function_identifier id, bs_exprs))

      else
        (* Closure *)
        let afs, a_expr = expression env a in
        let bfs, bs_exprs = expressions env bs in
        
        let call_expr = 
          define a_expr (fun closure_id ->
            let closure_var = T.Variable closure_id in
            T.UnknownFunCall (
              read_block closure_var (lint 0),
              closure_var :: bs_exprs
            )
          )
        in
        (afs @ bfs, call_expr)

      

    | S.IfThenElse (a, b, c) ->
      let afs, a = expression env a in
      let bfs, b = expression env b in
      let cfs, c = expression env c in
      afs @ bfs @ cfs, T.IfThenElse (a, b, c)

    | S.Fun (x, e) ->
      let raw_fvs = free_variables (S.Fun (x, e)) in 
    
      (* remove externals *)
      let fvs = List.filter (fun fv -> not (is_external fv env)) raw_fvs in
  
      let clo_p = make_fresh_variable () in
      let body_env = 
        (* Parameters directly accessibles *)
        let with_params = List.fold_left (fun env param ->
          { env with vars = Dict.insert param (T.Variable (identifier param)) env.vars }
        ) env x in
        (* Free variables *)
        let indexed_fvs = List.mapi (fun i fv -> (i, fv)) fvs in
        List.fold_left (fun env_acc (i, fv) ->
          let access = read_block (T.Variable clo_p) (lint (i + 1)) in
          { env_acc with vars = Dict.insert fv access env_acc.vars }
        ) with_params indexed_fvs
      in
      
      (* Translate the body *)
      let efs, body = expression body_env e in
      
      (* Create the toplevel function for the closure *)
      let f = make_fresh_function_identifier () in
      let def = T.DefineFunction (f, clo_p :: List.map identifier x, body) in
      
      (* Allocate the closure with the values of the free variables *)
      let closure_expr =
        define (allocate_block (lint (List.length fvs + 1))) (fun b ->
          let write_code = write_block (T.Variable b) (lint 0) (T.Literal (T.LFun f)) in
          let writes = List.mapi (fun i fv ->
            let fv_value = match Dict.lookup fv env.vars with
              | Some e -> e
              (* global variable *)
              | None -> T.Variable (identifier fv)
            in
            write_block (T.Variable b) (lint (i + 1)) fv_value
          ) fvs in
          seqs (write_code :: writes @ [T.Variable b])
        )
      in
      
      (efs @ [def], closure_expr)
     

    | S.AllocateBlock a ->
      let afs, a = expression env a in
      (afs, allocate_block a)
    | S.WriteBlock (a, b, c) ->
      let afs, a = expression env a in
      let bfs, b = expression env b in
      let cfs, c = expression env c in
      afs @ bfs @ cfs,
      T.FunCall (T.FunId "write_block", [a; b; c])
    | S.ReadBlock (a, b) ->
      let afs, a = expression env a in
      let bfs, b = expression env b in
      afs @ bfs,
      T.FunCall (T.FunId "read_block", [a; b])
    | S.Switch (a, bs, default) ->
      let afs, a = expression env a in
      let bsfs, bs =
        ExtStd.List.foldmap (fun bs t ->
                    match ExtStd.Option.map (expression env) t with
                    | None -> (bs, None)
                    | Some (bs', t') -> (bs @ bs', Some t')
                  ) [] (Array.to_list bs)
      in
      let dfs, default = match default with
        | None -> [], None
        | Some e -> let bs, e = expression env e in bs, Some e
      in
      afs @ bsfs @ dfs,
      T.Switch (a, Array.of_list bs, default)


  and expressions env = function
    | [] ->
       [], []
    | e :: es ->
       let efs, es = expressions env es in
       let fs, e = expression env e in
       fs @ efs, e :: es

  and literal = function
    | S.LInt x -> T.LInt x
    | S.LString s -> T.LString s
    | S.LChar c -> T.LChar c

  and identifier (S.Id x) = T.Id x

  and function_identifier (S.Id x) = T.FunId x

  (* Helper: Compile un groupe de fonctions mutuellement récursives *)
  (* Retourne : 
    - les définitions de fonctions globales (le code)
    - une liste (variable_fopix, expression_allocation)
    - une liste d'expressions d'initialisation (les write_block)
  *)
  and compile_recursive_group env fdefs =
    (* Prepare pointers for each function *)
    let fs_ids = List.map (fun (id, _) -> id) fdefs in
    let ptrs = List.map (fun _ -> make_fresh_variable ()) fdefs in

    (* Create recursive env *)
    let rec_env = List.fold_left2 (fun env id ptr ->
      { env with vars = Dict.insert id (T.Variable ptr) env.vars }
    ) env fs_ids ptrs in

    (* treat each func *)
    List.fold_left2 (fun (glob_acc, alloc_acc, init_acc) (_, expr) ptr ->
      match expr with 
      | S.Fun (args, body) ->
          (* calculate free variables *)
          let raw_fvs = free_variables expr in
          (* remove externals *)
          let fvs = List.filter (fun fv -> not (is_external fv env)) raw_fvs in
          (* compile body *)
          let self_id = make_fresh_variable () in
          let body_env = 
            let env_args = List.fold_left (fun env arg ->
              { env with vars = Dict.insert arg (T.Variable (identifier arg)) env.vars }
            ) rec_env args in
            
            List.fold_left (fun env (i, fv) ->
              let access = read_block (T.Variable self_id) (lint (i + 1)) in
              { env with vars = Dict.insert fv access env.vars }
            ) env_args (List.mapi (fun i fv -> (i, fv)) fvs)
          in

          let bfs, compiled_body = expression body_env body in
          
          (* Create global function *)
          let fun_label = make_fresh_function_identifier () in
          let global_def = T.DefineFunction (fun_label, self_id :: List.map identifier args, compiled_body) in

          (* Allocation of right size *)
          let alloc_expr = allocate_block (lint (List.length fvs + 1)) in

          (* Init *)
          let write_code = write_block (T.Variable ptr) (lint 0) (T.Literal (T.LFun fun_label)) in
          let writes = List.mapi (fun i fv ->
              let val_expr = match Dict.lookup fv rec_env.vars with
                | Some e -> e
                | None -> failwith ("Variable not found in recursive closure: " ^ (match fv with S.Id s -> s))
              in
              write_block (T.Variable ptr) (lint (i + 1)) val_expr
          ) fvs in
          
          (* Accumulate *)
          ( glob_acc @ bfs @ [global_def],
            alloc_acc @ [(ptr, alloc_expr)],
            init_acc @ [write_code] @ writes )

      | _ -> failwith "Recursive definitions must be functions"
    ) ([], [], []) fdefs ptrs

  in

  program env p
