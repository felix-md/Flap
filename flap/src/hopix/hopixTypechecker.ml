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
    try 
      let ts = List.map Position.value ts in
      let env' = HopixTypes.bind_type_variables pos env ts in
      let aty = HopixTypes.internalize_ty env' ty in
      let aty_scheme = HopixTypes.Scheme (ts, aty) in
      (aty_scheme, env')
    with HopixTypes.InvalidInstantiation ({expected=e ; given=g}) ->
    invalid_instantiation pos g e
      


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

    | PTuple pats ->
      match expected with 
      | HopixTypes.ATyTuple atys -> 
         List.fold_left2 (
          fun env pat expected -> 
            check_pattern env pat expected) 
            env pats atys

      |_ -> 
        HopixTypes.type_error pos "Wrong Tuple type" 
          






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
  | Fun fun_def -> synth_fun env fun_def
  | Define (vd,e) -> synth_define vd e env
  | Record (l,tys_opt) -> synth_record l tys_opt env
  | Field (expr, label, tys_opt) -> synth_field expr label tys_opt env
  | TypeAnnotation (e,ty) -> synth_type_annot env e ty
  | Ref expr -> synth_ref expr env
  | Assign (e1,e2) -> synth_assign e1 e2 env
  | Read expr -> synth_read expr env
  | Tagged (con,tys_opt,exprs) -> synth_tagged con tys_opt exprs env

  
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
    | HopixTypes.InvalidInstantiation ({given=g; expected =e}) ->
    invalid_instantiation pos g e

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


and synth_fun :
      HopixTypes.typing_environment ->
      HopixAST.function_definition ->
      HopixTypes.aty = 
      fun env fun_def ->
      let FunctionDefinition (pat, expr) = fun_def in 
      let (aty,env') = synth_pattern env pat 
      in 
      let body_ty = synth_expression env' expr
      in
       HopixTypes.ATyArrow (aty, body_ty)
       

      
    



and synth_define : 
    HopixAST.value_definition ->
    HopixAST.expression Position.located ->
    HopixTypes.typing_environment ->
    HopixTypes.aty
  = fun vd e env ->
    let new_env = check_value_definition env vd in 
    synth_expression new_env e

and synth_record :
    (HopixAST.label Position.located * HopixAST.expression Position.located) list ->
    HopixAST.ty Position.located list option ->
    HopixTypes.typing_environment ->
    HopixTypes.aty
  = fun fields tys_opt env ->

    (* Find constructor type with first label *)
    let (l0, _) = List.hd fields in
    let pos = Position.position l0 in
    let l0v = Position.value l0 in
    let (tycon, arity, expected_labels) =
      HopixTypes.lookup_type_constructor_of_label pos l0v env
    in

    (* Internalyze args type *)
    (* Args type should be explicit *)
    let arg_tys =
      match tys_opt with
      | None ->
          let (HopixAST.TCon tcname) = tycon in
          HopixTypes.type_error pos
            (Printf.sprintf
              "Missing type arguments for record of type %s."
              tcname)
      | Some tys ->
          let atylist = List.map (HopixTypes.internalize_ty env) tys in
          let given = List.length atylist in
          if given <> arity then
            invalid_instantiation pos given arity
          else
            atylist
    in

    (* Verify labels are valid and without duplicates *)
    let given_labels = List.map (fun (l, _) -> Position.value l) fields in
    let uniq_given = 
      let rec remove_dup acc = function
        | [] -> acc (* List is reverse, not a problem here*)
        (* Remove duplicates *)
        | x :: xs -> if List.mem x acc then remove_dup acc xs else remove_dup (x :: acc) xs
      in
      remove_dup [] given_labels
    in
    if List.length uniq_given <> List.length given_labels then
      HopixTypes.type_error pos "Duplicate labels in record literal.";

    let all_labels_ok =
      List.for_all (fun l -> List.mem l expected_labels) given_labels
    in
    if not all_labels_ok then
      HopixTypes.type_error pos "Unknown label in record literal.";

    (* For each field, verify the expected type with destructors *)
    try 
    let record_aty = HopixTypes.ATyCon (tycon, arg_tys) in
    List.iter
      (fun (lab, e) ->
         let labv = Position.value lab in
         (* Get the type scheme of the label *)
         let scheme = HopixTypes.lookup_type_scheme_of_label (Position.position lab) labv env in
         (* Apply substitution *)
         let fun_ty = HopixTypes.instantiate_type_scheme scheme arg_tys in 
         let (dom, cod) = HopixTypes.destruct_function_type (Position.position lab) fun_ty in
         (* Domain should be exactly the type of the instantiated record *)
         check_equal_types (Position.position lab) ~expected:record_aty ~given:dom;
         (* Verify that the field expression has the type of the field *)
         check_expression env e cod
      )
      fields;
    (* return the record type*)
    record_aty

    with HopixTypes.InvalidInstantiation ({given=g; expected = e}) ->
    invalid_instantiation pos g e


and synth_field :
      HopixAST.expression Position.located ->
      HopixAST.label Position.located ->
      HopixAST.ty Position.located list option ->
      HopixTypes.typing_environment ->
      HopixTypes.aty
  = fun expr label tys_opt env ->
  (* Determine record type *)
  let record_ty = synth_expression env expr in 
  let pos = label.position in 
  let label_id = label.value in 

  (* Get constructor types *)
  let (_, arg_tys) = HopixTypes.destruct_constructed_type pos record_ty in

  (* ? Should we do that *)

  let inter_tys = List.map ( HopixTypes.internalize_ty env )  (Option.value ~default:[] tys_opt)

  in if arg_tys <> inter_tys then 
    HopixTypes.type_error pos (Printf.sprintf "Type given differ from expected");

  (* Get the schme of the of label_id *)
  let label_scheme = 
    try
      HopixTypes.lookup_type_scheme_of_label pos label_id env
    with HopixTypes.Unbound (pos, label) ->
      HopixTypes.type_error pos (Printf.sprintf "Unbound %s." (HopixTypes.string_of_binding label))
  in

  (* Instantiate *)
  let arrow_ty = HopixTypes.instantiate_type_scheme label_scheme arg_tys in

  let (dom, cod) = HopixTypes.destruct_function_type pos arrow_ty in

  check_equal_types pos ~expected:dom ~given:record_ty;

  cod

and synth_ref :
      HopixAST.expression Position.located ->
      HopixTypes.typing_environment ->
      HopixTypes.aty
  = fun expr env ->
    let expr_ty = synth_expression env expr in
    HopixTypes.href expr_ty

and synth_assign :
      HopixAST.expression Position.located ->
      HopixAST.expression Position.located ->
      HopixTypes.typing_environment ->
      HopixTypes.aty
  = fun e1 e2 env ->
    (* Get the reference type *)
    let ref_ty = synth_expression env e1 in
    let ref_pos = Position.position e1 in

    (* Expected type for the content *)
    let content_ty = HopixTypes.destruct_reference_type ref_pos ref_ty in
    
    (* Check if good type for content *)
    check_expression env e2 content_ty;

    HopixTypes.hunit

and synth_read :
      HopixAST.expression Position.located ->
      HopixTypes.typing_environment ->
      HopixTypes.aty
  = fun expr env ->
    let ref_ty = synth_expression env expr in
    let ref_pos = Position.position expr in
    HopixTypes.destruct_reference_type ref_pos ref_ty

and synth_tagged :
      HopixAST.constructor Position.located ->
      HopixAST.ty Position.located list option ->
      HopixAST.expression Position.located list ->
      HopixTypes.typing_environment ->
      HopixTypes.aty
  = fun con tys_opt exprs env ->
    let con_pos = Position.position con in
    let con_id = Position.value con in
    
    (* Get constructor scheme *)
    let constructor_scheme = 
      try
        HopixTypes.lookup_type_scheme_of_constructor con_pos con_id env
      with HopixTypes.Unbound (pos,constructor) ->
        HopixTypes.type_error pos (Printf.sprintf "Unbound %s." (HopixTypes.string_of_binding constructor))
    in
    
    (* Internalyze arg_tys *)
    let arg_tys = 
      match tys_opt with
      | None ->
        HopixTypes.type_error con_pos "Missing type arguments for constructor."
      | Some ts ->
        List.map (HopixTypes.internalize_ty env) ts
    in

    (* Instantiate scheme with arg_tys *)
    let arrow_type = 
      try
        HopixTypes.instantiate_type_scheme constructor_scheme arg_tys
      with HopixTypes.InvalidInstantiation { expected; given; } ->
        invalid_instantiation con_pos given expected
    in

    (* Destruct to argument types and return type *)
    let (arg_tys, return_ty) = 
      HopixTypes.destruct_function_type_maximally con_pos arrow_type 
    in

    (* Verify arity of exprs and arg_tys *)
    
    if List.length exprs <> List.length arg_tys then
      HopixTypes.type_error con_pos "Invalid number of arguments provided to constructor.";
    
    (* Verify each elements of exprs with arg_tys *)
    List.iter2 (fun expr expected_ty ->
      check_expression env expr expected_ty
    ) exprs arg_tys;

    (* synth return type *)
    return_ty
    





and synth_type_annot :
  HopixTypes.typing_environment ->
  HopixAST.expression Position.located ->
  HopixAST.ty Position.located ->
  HopixTypes.aty = 
  fun env expr ty ->
    let aty = HopixTypes.internalize_ty env ty
    in
    check_expression env expr aty;
    aty




and check_expression :
      HopixTypes.typing_environment ->
      HopixAST.expression Position.located ->
      HopixTypes.aty ->
      unit
  = fun env (Position.{ value = e; position = pos; } as exp) expected ->
  match e with
  | Fun (FunctionDefinition (pat, body)) ->
      (match expected with
       | HopixTypes.ATyArrow (dom, cod) ->
          let env' = check_pattern env pat dom in
          check_expression env' body cod
       | _ ->
          let given = synth_expression env exp in
          check_equal_types pos ~expected ~given
      )
  | _ ->
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
