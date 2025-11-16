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
    match value with
    | PWildcard | PLiteral _ -> vars
    | PVariable id ->
      if List.mem (id.value) vars then 
        HopixTypes.type_error position 
          (Printf.sprintf "Variable `%s' is bound multiple times in this pattern." 
             (let (Id s) = id.value in s))
      else
        (id.value) :: vars
    | PTypeAnnotation (pat, _) -> check_pattern_linearity vars pat
    | PTaggedValue (_, _, pats) | PTuple pats  | PAnd pats->
       List.fold_left check_pattern_linearity vars pats
    | PRecord (fields, _) ->
        List.fold_left (fun vars (_,pat) -> check_pattern_linearity vars pat) vars fields

    | POr pats ->
      (* For disjunctive patterns, we check that all branches bind the same variables *)
      let all_set = List.map (check_pattern_linearity vars ) pats in (* List of List of vars, one per branch *)
      if List.exists (fun branch -> branch <> List.hd all_set) all_set then 
        HopixTypes.type_error position 
          "In a disjunctive pattern, all branches must bind the same set of variables."
      else
        List.hd all_set
      






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


let  synth_literal : HopixAST.literal -> HopixTypes.aty =
  fun l ->
    match l with
    | LInt _ -> HopixTypes.hint
    | LString _ -> HopixTypes.hstring
    | LChar _ -> HopixTypes.hchar


let rec check_pattern :
          HopixTypes.typing_environment ->
          HopixAST.pattern Position.located ->
          HopixTypes.aty ->
          HopixTypes.typing_environment
  = fun env Position.({ value = p; position = pos; } as pat) expected ->
    let _ = check_pattern_linearity [] pat in
    match p with 
    | PWildcard -> env
    | PVariable id ->
        HopixTypes.bind_value (Position.value id) (HopixTypes.monomorphic_type_scheme expected) env 
    | PAnd pats | POr pats ->
        List.fold_left (fun env pat -> check_pattern env pat expected) env (pats)


    | PLiteral _ | PTypeAnnotation _ | PTaggedValue _ | PRecord _ ->
        let (given,env') = synth_pattern env pat in
        check_equal_types pos ~expected ~given;
        env'

    | _ ->
        failwith "Other cases of check_pattern not implemented yet." 






and synth_pattern :
      HopixTypes.typing_environment ->
      HopixAST.pattern Position.located ->
      HopixTypes.aty * HopixTypes.typing_environment
  = fun env (Position.{ value = p; position = pos; } as pat) ->
    let _ = check_pattern_linearity [] pat in
    match p with
    | PLiteral l ->
        let aty = synth_literal (Position.value l) in
        (aty, env)
    | PTypeAnnotation (pat,ty) ->
        let ty = HopixTypes.internalize_ty env ty in
        let env' = check_pattern env pat ty in
        (ty , env')

    | PTuple pats -> List.fold_left 
      (fun (tys, env) pat ->
        let (ty, env') = synth_pattern env pat  in
        (ty :: tys, env')
      ) ([], env) pats
      |> fun (tys, env') -> (HopixTypes.ATyTuple tys, env')


    | _ ->
        failwith "Other cases of synth_pattern not implemented yet."







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
      failwith "Other cases of synth_expression not implemented yet."






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
      let args_types = List.map (HopixTypes.internalize_ty env) (Option.value tys_opt ~default:[]) in
      HopixTypes.instantiate_type_scheme scheme args_types

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
        (Printf.sprintf "This expression has type %s which should be a function type." (HopixTypes.string_of_aty f_ty))


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
  
  | RecFunctions fun_defs -> check_rec_functions env fun_defs

        
and check_rec_functions : 
      HopixTypes.typing_environment ->
      HopixAST.function_definition polymorphic_definition list ->
      HopixTypes.typing_environment
  = fun env fun_defs ->

    (* First we bind all function names with their type schemes and check missing annotations *)
    let env =
      List.fold_left
        (fun env (id, type_scheme_opt,_) ->
           let aty_scheme =
             match type_scheme_opt with
             | Some ts ->
                let (aty_scheme, _) = Position.located_pos (check_type_scheme env) ts in
                aty_scheme
             | None ->
                failwith "Function definitions must be annotated with a type scheme."
           in
           HopixTypes.bind_value (Position.value id) aty_scheme env
        ) env fun_defs

      in 
      (* Then we check that the function are really of the annotated type *)

      List.iter (fun (f, fs, d) ->
        match fs with
        | None ->
          (* This case is now impossible cause of the previous pass *)
           assert false
        | Some fs ->
           let pos = Position.position f in
           check_function_definition pos env fs d
      )  fun_defs;
      env 




and check_function_definition :
      Position.t ->
      HopixTypes.typing_environment ->
      HopixAST.type_scheme Position.located ->
      HopixAST.function_definition ->
      unit
  = fun pos env ts (FunctionDefinition (pat, body)) ->
    let (aty_scheme, env) = Position.located_pos (check_type_scheme env) ts in
    match aty_scheme with
    | HopixTypes.Scheme (_, aty) ->
       (match aty with
        | HopixTypes.ATyArrow (dom, cod) ->
           let env' = check_pattern env pat dom in
           check_expression env' body cod
        | _ ->
           HopixTypes.type_error pos
             "Function type scheme must be of arrow type."
       )





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
