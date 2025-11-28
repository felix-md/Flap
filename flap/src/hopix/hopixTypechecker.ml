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

(** Utility functions *)

(* Generic function to instantiate both constructors and identifiers *)
let check_instantiate : 
    'a Position.located ->
    HopixAST.ty Position.located list option ->
    (Position.t -> 'a -> HopixTypes.typing_environment -> HopixTypes.aty_scheme) ->
    HopixTypes.typing_environment -> 
    HopixTypes.aty =
    fun id tys_opt lookup env ->
  let value, pos = Position.destruct id in
  let Scheme(args, con_ty) =
    try
      lookup pos value env
    with HopixTypes.Unbound (err_pos, err_cons) ->
      HopixTypes.type_error err_pos (Printf.sprintf "Unbound %s." (HopixTypes.string_of_binding err_cons))
  in

  let args_len = List.length args in

  let args_types = match tys_opt with
  | None -> if args_len <> 0 then
      invalid_instantiation pos 0 args_len
    else
      []
  | Some tys ->
      let given_len = List.length tys in
      if given_len <> args_len then
        invalid_instantiation pos given_len args_len
      else
        List.map (HopixTypes.internalize_ty env) tys
  in

  try
    HopixTypes.instantiate_type_scheme (HopixTypes.Scheme (args, con_ty)) args_types
  with HopixTypes.InvalidInstantiation {given; expected} ->
    invalid_instantiation pos given expected

(* Specialized version for constructors *)
let check_instantiate_of_constructor id tys_opt env =
  check_instantiate id tys_opt HopixTypes.lookup_type_scheme_of_constructor env

(* Specialized version for identifiers *)
let check_instantiate_of_identifier id tys_opt env =
  check_instantiate id tys_opt HopixTypes.lookup_type_scheme_of_identifier env


(* Specialized version for labels *)
let check_instantiate_of_label label tys_opt env = 
  check_instantiate label tys_opt HopixTypes.lookup_type_scheme_of_label env

(** Linearity-checking code for patterns *)

let rec check_pattern_linearity
        : identifier list -> pattern Position.located -> identifier list
  = fun vars Position.{ value; position; } ->
    match value with
    | PWildcard | PLiteral _ -> vars
    | PVariable id ->
      if List.mem (id.value) vars then 
        HopixTypes.type_error position 
          (Printf.sprintf "The variable %s has already appeared in this pattern." 
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

    | _ -> 
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

    | PTuple pats -> 
      begin
      List.fold_left 
      (fun (tys, env) pat ->
        let (ty, env') = synth_pattern env pat  in
        (ty :: tys, env')
      ) ([], env) pats
      |> fun (tys, env') -> (HopixTypes.ATyTuple tys, env')
      end

    | POr pats ->
      begin 
      let (first_ty, env') = synth_pattern env (List.hd pats) in
      List.iter (fun pat ->
        let (ty, _) = synth_pattern env' pat in
        if ty <> first_ty then 
          HopixTypes.type_error pos 
            "In a disjunctive pattern, all branches must have the same type."
      ) pats;
      (first_ty, env')
    end
    | PTaggedValue (cons, tys_opt, pats) -> 
      let  inst_ty = 
       check_instantiate_of_constructor cons tys_opt env 
      in
      let (arg_tys, return_ty) = 
        HopixTypes.destruct_function_type_maximally pos inst_ty 
      in
      let env' =
        List.fold_left2 (fun env pat expected_ty ->
          check_pattern env pat expected_ty
        ) env pats arg_tys
      in
      (return_ty, env')

    | PRecord (fields, tys_opt) -> 
      let (l0, _) = List.hd fields in
      let l0_pos = Position.position l0 in
      let l0v = Position.value l0 in 

      let (tycon, arity, expected_labels) =
      try
        HopixTypes.lookup_type_constructor_of_label l0_pos l0v env
      with HopixTypes.Unbound (_, binding) ->
        HopixTypes.type_error l0_pos (Printf.sprintf "There is no type definition for %s." (HopixTypes.string_of_binding binding))
      in
      
      (* Handle arg types *)
      let arg_tys =
        match tys_opt with
        | None ->
             let (HopixAST.TCon tcname) = tycon in
             HopixTypes.type_error pos
               (Printf.sprintf "Missing type arguments for record pattern of type %s." tcname)
        | Some ts ->
             let atys = List.map (HopixTypes.internalize_ty env) ts in
             let given = List.length atys in
             if given <> arity then
               invalid_instantiation pos given arity
             else
               atys
      in

      (* Verify unicity *)
      let given_labels = List.map (fun (l, _) -> Position.value l) fields in
      
      (* Verify duplicate *)
      if List.length (List.sort_uniq compare given_labels) <> List.length given_labels then
        HopixTypes.type_error pos "Duplicate labels in record pattern.";

      (* Verify given_labels in expected_labels *)
      if not (List.for_all (fun l -> List.mem l expected_labels) given_labels) then
        HopixTypes.type_error pos "Unknown label in record pattern.";

      (* Verify pattern *)
      let record_aty = HopixTypes.ATyCon (tycon, arg_tys) in

      let final_env = 
        List.fold_left (fun curr_env (lbl_loc, sub_pat) ->

          let field_arrow_ty = check_instantiate_of_label lbl_loc tys_opt curr_env in
          
          let (_, field_ty) = HopixTypes.destruct_function_type lbl_loc.position field_arrow_ty in
          
          check_pattern curr_env sub_pat field_ty

        ) env fields
      in

      (* Return the type of the record and the final environment *)
      (record_aty, final_env)

    | _ -> assert false 
    (* PWildcard, PVariable and PAnd synth are not implemented *)
    





let rec synth_expression :
      HopixTypes.typing_environment ->
      HopixAST.expression Position.located ->
      HopixTypes.aty
  = fun env Position.{ value = e; position = _; } ->
  match e with
  | Literal l -> synth_literal (Position.value l)
  | Variable (id,tys_opt) -> synth_variable id tys_opt  env
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
  | Sequence exprs -> synth_sequence env exprs
  | IfThenElse (cond , t_branch, f_branch) -> synth_if_then_else env cond t_branch f_branch
  | Tuple exprs ->  synth_tuple env exprs
  | Case ( expr, branchs) -> synth_case env expr branchs 
  | While (e1,e2) -> synth_while e1 e2 env
  | For (id,e2,e3,e4) -> synth_for id e2 e3 e4 env

  
   


and synth_variable : 
    HopixAST.identifier Position.located ->
    HopixAST.ty  Position.located list option ->
    HopixTypes.typing_environment ->
    HopixTypes.aty
    = fun id tys_opt  env  ->
    check_instantiate_of_identifier id tys_opt env

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
    let given_labels = List.map (fun (l, _) -> Position.value l) fields 
    in
    if List.length (List.sort_uniq compare given_labels )<> List.length given_labels then
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
         check_expression env e  cod)
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
  let pos = label.position in 
  let arrow_ty = 
    check_instantiate_of_label label tys_opt env
  in
  let (dom, cod) = HopixTypes.destruct_function_type pos arrow_ty in
  check_expression env expr dom;
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
   

    let arrow_type = 
      check_instantiate_of_constructor con tys_opt env
    in 

    let con_pos = Position.position con in 

    (* Destruct to argument types and return type *)
    let (arg_tys', return_ty) = 
      HopixTypes.destruct_function_type_maximally (Position.position con) arrow_type 
    in

    (* Handle argument count and type checking *)
    let nb_given = List.length exprs in
    let nb_expected = List.length arg_tys' in
    
     if nb_given > nb_expected then begin
      (* check what we can *)
      List.iter2 (fun expr expected_ty ->
        check_expression env expr expected_ty
      ) (List.filteri (fun i _ -> i < nb_expected) exprs) arg_tys';
      
      (* Build the result type after consuming all expected arguments *)
      let base_type = return_ty in
      
      (* Now synthesize applications for the remaining arguments *)
      let remaining_exprs = List.filteri (fun i _ -> i >= nb_expected) exprs in
      List.fold_left (fun acc_ty expr ->
        (* Try to decompose acc_ty as a function type *)
        let arg_ty, ret_ty = HopixTypes.destruct_function_type con_pos acc_ty in
        check_expression env expr arg_ty;
        ret_ty
      ) base_type remaining_exprs
    end 
  
   
  else if nb_given = nb_expected then begin
      (* Full application: check all arguments and return the final type *)
      List.iter2 (fun expr expected_ty ->
        check_expression env expr expected_ty
      ) exprs arg_tys';
      return_ty
    end 
  
  
  else begin
      (* Partial application: check provided arguments and return remaining function type *)
      let arg_tys_to_check, remaining_arg_tys = 
        let rec split n acc = function
          | [] -> (List.rev acc, [])
          | xs when n = 0 -> (List.rev acc, xs)
          | x :: xs -> split (n - 1) (x :: acc) xs
        in
        split nb_given [] arg_tys'
      in
      List.iter2 (fun expr expected_ty ->
        check_expression env expr expected_ty
      ) exprs arg_tys_to_check;
      List.fold_right (fun arg_ty acc -> HopixTypes.ATyArrow (arg_ty, acc)) 
        remaining_arg_tys return_ty
    end
    

and synth_sequence :
      HopixTypes.typing_environment ->
      HopixAST.expression Position.located list ->
      HopixTypes.aty = 
      fun env exprs->
      let rev_exprs = List.rev exprs in
      List.iter (fun e ->  ignore (synth_expression env e)   ) (List.tl rev_exprs);
      synth_expression env (List.hd rev_exprs)

and synth_if_then_else :
      HopixTypes.typing_environment ->
      HopixAST.expression Position.located ->
      HopixAST.expression Position.located ->
      HopixAST.expression Position.located ->
      HopixTypes.aty = 
      fun env cond t_branch f_branch ->
      check_expression env cond HopixTypes.hbool;
      let t_ty = synth_expression env t_branch in
      check_expression env f_branch t_ty;
      t_ty



and synth_tuple :
      HopixTypes.typing_environment ->
      HopixAST.expression Position.located list ->
      HopixTypes.aty = 
      fun env exprs ->
      let (tys) = List.map 
      (fun expr -> 
        synth_expression env expr  
      ) exprs
      in
      HopixTypes.ATyTuple tys


and synth_case : 
      HopixTypes.typing_environment ->
      HopixAST.expression Position.located ->
      HopixAST.branch Position.located list ->
      HopixTypes.aty =
      fun env expr branchs ->
        let expr_ty = synth_expression env expr in
        let branch_tys = 
          List.map (fun Position.{ value = (Branch (pat, body)); position = _; } ->
            let env' = check_pattern env pat expr_ty in
            synth_expression env' body
          ) branchs
        in
        match branch_tys with
        | [] -> HopixTypes.type_error (Position.position expr) "Case expression must have at least one branch."
        | first_ty :: rest_tys ->
            List.iter (fun ty ->
              if ty <> first_ty then
                HopixTypes.type_error (Position.position expr) "All branches of a case expression must have the same type."
            ) rest_tys;
            first_ty

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

and synth_while :
      HopixAST.expression Position.located ->
      HopixAST.expression Position.located ->
      HopixTypes.typing_environment ->
      HopixTypes.aty
  = fun e1 e2 env ->
    check_expression env e1 HopixTypes.hbool;
    check_expression env e2 HopixTypes.hunit;
    HopixTypes.hunit

and synth_for :
      HopixAST.identifier Position.located ->
      HopixAST.expression Position.located ->
      HopixAST.expression Position.located ->
      HopixAST.expression Position.located ->
      HopixTypes.typing_environment ->
      HopixTypes.aty
  = fun id e2 e3 e4 env ->
    check_expression env e2 HopixTypes.hint;
    check_expression env e3 HopixTypes.hint;
    let env' = HopixTypes.bind_value (Position.value id) (HopixTypes.monomorphic_type_scheme HopixTypes.hint) env in
    check_expression env' e4 HopixTypes.hunit;
    HopixTypes.hunit

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


  | IfThenElse (cond, t_branch, f_branch) ->
    check_expression env cond HopixTypes.hbool;
    check_expression env t_branch expected ;
    check_expression env f_branch expected

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
          let (aty_scheme, env) = Position.located_pos (check_type_scheme env) ts in
          let expected_ty = 
            match aty_scheme with
            | HopixTypes.Scheme (_, ty) -> ty
          in
          check_expression env expr expected_ty;
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
