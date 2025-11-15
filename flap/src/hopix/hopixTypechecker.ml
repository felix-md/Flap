(** This module implements a bidirectional type checker for Hopix. *)

open HopixAST

(** Error messages *)

let invalid_instantiation pos given expected =
  HopixTypes.type_error pos (
      Printf.sprintf
        "Invalid number of types in instantiation: \
         %d given while %d were expected." given expected
    )

let check_equal_types pos ~expected ~given =
  if expected <> given
  then
    HopixTypes.(type_error pos
                  Printf.(sprintf
                            "Type mismatch.\nExpected:\n  %s\nGiven:\n  %s"
                            (string_of_aty expected)
                            (string_of_aty given)))

(** Linearity-checking code for patterns *)

let rec check_pattern_linearity
        : identifier list -> pattern Position.located -> identifier list
  = fun vars Position.{ value; position; } ->
  failwith "Students! This is your job!"

(** Type-checking code *)

let check_type_scheme :
      HopixTypes.typing_environment ->
      Position.t ->
      HopixAST.type_scheme ->
      HopixTypes.aty_scheme * HopixTypes.typing_environment
  = fun env pos (ForallTy (ts, ty)) -> 
    let ts = List.map Position.value ts in
    let env' = HopixTypes.bind_type_variables pos env ts in
    let aty = HopixTypes.internalize_ty env' ty in
    let aty_scheme = HopixTypes.Scheme (ts, aty) in
    (aty_scheme, env')





let rec check_pattern :
          HopixTypes.typing_environment ->
          HopixAST.pattern Position.located ->
          HopixTypes.aty ->
          HopixTypes.typing_environment
  = fun env Position.({ value = p; position = pos; } as pat) expected ->
  failwith "Students! This is your job!"

and synth_pattern :
      HopixTypes.typing_environment ->
      HopixAST.pattern Position.located ->
      HopixTypes.aty * HopixTypes.typing_environment
  = fun env Position.{ value = p; position = pos; } ->
  failwith "Students! This is your job!"

let rec synth_expression :
      HopixTypes.typing_environment ->
      HopixAST.expression Position.located ->
      HopixTypes.aty
  = fun env Position.{ value = e; position = pos; } ->
  match e with
  | Literal l ->
      synth_literal (Position.value l)
  | Variable (id,tys_opt) -> synth_variable id tys_opt pos env

  | Apply (f,x) -> synth_apply f x env  
  | Fun fun_def -> failwith "synth Fun"
  | Define (vd,e) -> synth_define vd e env
  | Record (l,tys_opt) -> failwith "synth Record"
  | TypeAnnotation (e,ty) -> failwith "synth TypeAnnotation"
  
  | _ ->
      failwith "Students! This is your job!"

and synth_literal : HopixAST.literal -> HopixTypes.aty =
  fun l ->
    match l with
    | LInt _ -> HopixTypes.hint
    | LString _ -> HopixTypes.hstring
    | LChar _ -> HopixTypes.hchar




and synth_variable : 
    HopixAST.identifier Position.located ->
    HopixAST.ty  Position.located list option ->
    Position.t ->
    HopixTypes.typing_environment ->
    HopixTypes.aty
    = fun id tys_opt pos env  ->

    let id_value = Position.value id in 
    try 
      let scheme = HopixTypes.lookup_type_scheme_of_identifier pos id_value env in
      match tys_opt with
      | Some ts -> begin
        let args_types = List.map (HopixTypes.internalize_ty env)  ts
      in 
      HopixTypes.instantiate_type_scheme scheme args_types
    end
      | None -> 
        let Scheme (type_vars, _) = scheme in
        print_int (List.length type_vars);

        HopixTypes.instantiate_type_scheme scheme []
    with HopixTypes.Unbound _ ->
      HopixTypes.type_error pos 
        (Printf.sprintf "Unbound identifier `%s'." ((fun (Id s) -> s) id_value))

and synth_apply : 
    HopixAST.expression Position.located ->
    HopixAST.expression Position.located ->
    HopixTypes.typing_environment ->
    HopixTypes.aty
  = fun f x env ->
    let f_ty = synth_expression env f in 
    match f_ty with 
    | HopixTypes.ATyArrow (dom, cod) ->
      check_expression env x dom; cod
    | _ -> 
      HopixTypes.type_error (f.position) 
        (Printf.sprintf "Expected a function type, but got `%s'." 
          (HopixTypes.string_of_aty f_ty))


and synth_define : 
    HopixAST.value_definition ->
    HopixAST.expression Position.located ->
    HopixTypes.typing_environment ->
    HopixTypes.aty
  = fun vd e env ->
    let new_env = check_value_definition env vd in 
    synth_expression new_env e

and check_expression :
      HopixTypes.typing_environment ->
      HopixAST.expression Position.located ->
      HopixTypes.aty ->
      unit
  = fun env (Position.{ value = e; position = pos; } as exp) expected ->
  let given = synth_expression env exp in
  check_equal_types pos ~expected ~given

and check_value_definition :
      HopixTypes.typing_environment ->
      HopixAST.value_definition ->
      HopixTypes.typing_environment
  = fun env def ->
  match def with
  | SimpleValue (id, type_scheme_opt, expr) ->
      (match type_scheme_opt with
       (* Annotated with a type scheme *)
       | Some ts ->
          (* verify type scheme *)
          let (aty_scheme, env) = Position.located_pos (check_type_scheme env) ts in
          let expected_ty = 
            match aty_scheme with
            | HopixTypes.Scheme (_, ty) -> ty
          in
          (* check expression *)
          check_expression env expr expected_ty;
          (* bind aty_scheme to to env *)
          HopixTypes.bind_value (Position.value id) aty_scheme env
       
       | None ->
          (* Not annotated : synth expression type *)
          let ty = synth_expression env expr in
          (* Generalize *)
          let scheme = HopixTypes.generalize_type env ty in
          HopixTypes.bind_value (Position.value id) scheme env
      )
  
  | RecFunctions _ ->
      failwith "Not implemented yet"


let check_definition env = function
  | DefineValue vdef ->
     check_value_definition env vdef

  | DefineType (t, ts, tdef) ->
     let ts = List.map Position.value ts in
     HopixTypes.bind_type_definition (Position.value t) ts tdef env

  | DeclareExtern (x, tys) ->
     let tys, _ = Position.located_pos (check_type_scheme env) tys in
     HopixTypes.bind_value (Position.value x) tys env

let typecheck env program =
  List.fold_left
    (fun env d -> Position.located (check_definition env) d)
    env program

type typing_environment = HopixTypes.typing_environment

let initial_typing_environment = HopixTypes.initial_typing_environment

let print_typing_environment = HopixTypes.string_of_typing_environment
