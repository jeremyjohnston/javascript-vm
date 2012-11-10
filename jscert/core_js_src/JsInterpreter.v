Set Implicit Arguments.
Require Import Shared.
Require Import LibFix.
Require Import JsSemanticsAux JsWf JsWfAux JsScopes JsSafety.

(**************************************************************)
(** ** TODO: move (to discuss) *)

Section Memory.

Definition fresh_for_list (h : list (ref * value)) : loc :=
  loc_normal (S (fold_left (fun r n =>
    match r with (Ref l f, _) =>
      match l with
      | loc_normal n' => max n n'
      | _ => n
      end
    end
  ) 0%nat h)).

Parameter fresh_for : heap -> loc.
Parameter fresh_for_spec : forall h, fresh h (fresh_for h).
Parameter fresh_for_normal : forall h, exists n, fresh_for h = loc_normal n.

End Memory.


(**************************************************************)
(** ** Implementation of [basic_value] and [value_comparable] *)

Definition basic_value_bool v :=
  match v with
  | value_undef | value_bool _ | value_number _ | value_string _ | value_loc loc_null => true
  | _ => false
  end.

Instance basic_value_decidable : forall v,
  Decidable (basic_value v).
Proof.
  introv. applys decidable_make (basic_value_bool v). extens.
  iff H.
  destruct* v; tryfalse;
    rewrite istrue_def in H; inverts* H; apply* istrue_isTrue_back.
  destruct* l; false.
  destruct* v; tryfalse; forwards H0: istrue_isTrue_forw H;
    rewrite istrue_def; inverts* H0.
Qed.

Lemma value_compare_correct : forall v1 v2, 
  basic_value v1 -> basic_value v2 ->
  value_compare v1 v2 = isTrue (v1 = v2).
Proof.
  introv BV1 BV2. extens.
  destruct v1; destruct v2; simpl; rew_refl; 
   try solve [ iff M; tryfalse; auto; try congruence ].
  inverts BV1.
  inverts BV2.
Qed.

Global Instance value_comparable : forall v1 v2,
  basic_value v1 -> basic_value v2 ->
  Decidable (v1 = v2).
Proof.
  introv BV1 BV2. applys decidable_make (value_compare v1 v2).
  apply* value_compare_correct.
Qed.


(**************************************************************)
(** ** Implementation of [proto_comp], which computes [proto] *)

Section Proto.

(** Definition of [proto_comp] *)

Definition proto_comp_body proto_comp h f l :=
  ifb l = loc_null then loc_null
  else ifb indom h l f then l
  else ifb indom h l field_proto then
    match read h l field_proto with
    | value_loc l' => proto_comp h f l'
    | _ => arbitrary
    end
  else arbitrary.
 
Definition proto_comp := FixFun3 proto_comp_body.

End Proto.


(**************************************************************)
(** ** Implementation of [scopes] *)

Section Scopes.

(** Definition of [scope_comp] *)

Fixpoint scope_comp h (f : field) (L : scope) : loc :=
  match L with
  | nil => loc_null
  | cons l s =>
    let l' := proto_comp h f l in
    ifb l' = loc_null then scope_comp h f s else l
  end.

End Scopes.


(**************************************************************)
(** ** Implementation of [getvalue] *)

Section Getvalue.

(** Definition of [getvalue_comp] *)

Definition getvalue_comp h r :=
  match r with
  | result_value v => Some v
  | result_ref (Ref l f) =>
    match f with
    | field_normal _ =>
      ifb l = loc_null then None (* LATER: throws exception "cannot read property 'f' of null" *)
      else
        let l' := proto_comp h f l in
        ifb l' = loc_null then Some value_undef
        else Some (read h l' f)
    | _ => None
    end
  end.

End Getvalue.


(**************************************************************)
(** ** Helper functions for the interpreter *)

Section InterpreterEliminations.

Parameter Mnostuck : bool.

Inductive ret :=
  | ret_result : result -> ret
  | ret_exn : result -> ret.

Inductive out :=
  | out_return : heap -> ret -> out
  | out_unspec : out
  | out_bottom : out.

Definition make_error (h : heap) s :=
  out_return h (ret_exn (result_value (value_string s))).
Definition ret_value v := ret_result (result_value v).
Definition ret_ref l f := ret_result (result_ref (Ref l f)).

Definition wrong h :=
  if Mnostuck then make_error h "No reduction rule can be applied."
  else out_unspec.

Definition if_success o (k : heap -> result -> out) :=
  match o with
  | out_return h (ret_result v) => k h v
  | _ => o
  end.

Definition if_fault o (k : heap -> result -> out) :=
  match o with
  | out_return h (ret_exn v) => k h v
  | _ => o
  end.

Definition if_defined A h o (k : A -> out) :=
  match o with
  | None => wrong h
  | Some a => k a
  end.

Definition if_success_value o k :=
  if_success o (fun h1 r1 =>
    if_defined h1 (getvalue_comp h1 r1) (k h1)).

Definition if_is_value (h : heap) r k :=
  match r with
  | result_value v => k v
  | result_ref _ => wrong h
  end.

Definition if_is_ref (h : heap) r k :=
  match r with
  | result_value _ => wrong h
  | result_ref (Ref l f) => k l f
  end.

Definition if_is_field_normal h f k :=
  match f with
  | field_normal f => k f
  | _ => wrong h
  end.

Definition if_basic_value (h : heap) v k :=
  ifb basic_value v then k else wrong h.

Definition if_eq l0 h o (k1 : True -> out) (k2 : loc -> out) :=
  if_defined h o (fun v =>
    match v with
    | value_loc l => ifb l = l0 then k1 I else k2 l
    | _ => wrong h
    end).

Definition if_not_eq l0 h o k :=
  if_eq l0 h o (fun _ => wrong h) k.

Definition if_is_null_ref r (k1 : field -> out) k2 :=
  match r with
  | result_value _ => k2 r
  | result_ref (Ref l f) =>
    ifb l = loc_null then k1 f else k2 r
  end.

Definition if_is_string h o (k : string -> out) :=
  if_defined h o (fun v =>
    match v with
    | value_string s => k s
    | _ => wrong h
    end).

Definition if_is_loc h o (k : loc -> out) :=
  if_defined h o (fun v =>
    match v with
    | value_loc l => k l
    | _ => wrong h
    end).

Definition if_binds_field f h l k :=
  ifb indom h l f
    then k (read h l f)
    else wrong h.

Definition if_binds_scope_body h l k :=
  if_binds_field field_scope h l (fun v =>
    match v with
    | value_scope s =>
      if_binds_field field_body h l (fun v' =>
        match v' with
          | value_body f e => k s f e
          | _ => wrong h
        end)
    | _ => wrong h
    end).

Definition if_binds_field_loc f h l k :=
  if_binds_field f h l (fun v =>
    match v with
    | value_loc l' => k l'
    | _ => wrong h
    end).

Definition if_boolean h v e1 e2 :=
  match v with
    | value_bool true => e1 I
    | value_bool false => e2 I
    | _ => wrong h
  end.

Definition if_convert_to_bool h v e1 e2 :=
  if_boolean h v e1 e2. (* Later: Type conversion. *)

End InterpreterEliminations.

Section Flags.


(**************************************************************)
(** ** Implementation of operators *)

Definition dont_delete_comp r : bool :=
  match r with
  | result_value _ => false
  | result_ref (Ref l f) =>
    match f with
    | field_proto | field_this | field_scope => true
    | field_normal f => decide (f = "prototype"%string)
    | _ => false
    end
  end.

Global Instance dont_delete_comparable : forall r,
  Decidable (dont_delete r).
Proof.
  introv. applys decidable_make (dont_delete_comp r). destruct r.
   simpl. symmetry. apply* isTrue_false.
  destruct r. destruct f; simpl.
   tests: (s = "prototype"%string).
    rewrite decide_spec. rewrite eqb_self.
     symmetry. apply* isTrue_true.
    rewrite decide_spec. rewrite~ eqb_neq.
     symmetry. apply* isTrue_false.
     introv [H | [H | [H | H]]]; inverts~ H.
   symmetry. apply* isTrue_true.
   symmetry. apply* isTrue_false.
    introv [H | [H | [H | H]]]; inverts~ H.
   symmetry. apply* isTrue_true.
   symmetry. apply* isTrue_true.
Qed.

End Flags.

Section Interpreter.

Definition if_is_loc_value v (f : loc -> option value) :=
  match v with
  | value_loc l => f l
  | _ => None
  end.

Definition binary_op_comp_body binary_op_comp b h v1 v2 :=
  match b with
  | binary_op_equal =>
    ifb basic_value v1 /\ basic_value v2 then
      Some (value_bool (value_compare v1 v2))
    else None
  | binary_op_add =>
    match v1, v2 with
    | value_number n1, value_number n2 => Some (value_number (number_add n1 n2))
    | value_string s1, value_string s2 => Some (value_string (s1 ++ s2))
    | _, _ => None (* Type coercions are not performs yet. *)
    end
  | binary_op_mult =>
    match v1, v2 with
    | value_number n1, value_number n2 => Some (value_number (number_mult n1 n2))
    | _, _ => None (* Type coercions are not performs yet. *)
    end
  | binary_op_div =>
    match v1, v2 with
    | value_number n1, value_number n2 => Some (value_number (number_div n1 n2))
    | _, _ => None (* Type coercions are not performs yet. *)
    end
  | binary_op_in =>
    match v1, v2 with
    | value_string f, value_loc l => Some (value_bool
      (neg (decide ((proto_comp h (field_normal f) l) = loc_null))))
    | _, _ => None
    end
  | binary_op_instanceof =>
    if_is_loc_value v1 (fun l1 =>
      ifb basic_value v2 then Some (value_bool false)
      else match v2 with
         | value_loc l2 =>
           ifb indom h l1 field_normal_prototype then
             if_is_loc_value (read h l1 field_normal_prototype) (fun l3 =>
               ifb indom h l2 field_proto then
                 if_is_loc_value (read h l2 field_proto) (fun l4 =>
                   ifb l3 = l4 then
                     Some (value_bool true)
                   else
                     binary_op_comp binary_op_instanceof h (value_loc l1) (value_loc l4)
                 )
               else None
             )
           else None
         | _ => None
         end)
  end.

Definition binary_op_comp := FixFun4 binary_op_comp_body.

Definition unary_op_comp u (h : heap) v :=
  match u with
  | unary_op_void => Some value_undef
  | unary_op_not =>
    match v with
    | value_bool b => Some (value_bool (neg b))
    | _ => None
    end
  | _ => None
  end.

Definition typeof_comp h v :=
  match v with
  | value_undef => Some "undefined"%string
  | value_bool b => Some "boolean"%string
  | value_number n => Some "number"%string
  | value_string f => Some "string"%string
  | value_scope s => None
  | value_body f e => None
  | value_loc l =>
    ifb indom h l field_body then Some "function"%string
    else Some "object"%string
  end.

Fixpoint arguments_comp (lx : list string) (lv : list value) : list (field * value) :=
  match lx with
  | nil => nil
  | x :: lx' =>
    match lv with
    | nil =>
      (field_normal x, value_undef) :: arguments_comp lx' nil
    | v :: lv' =>
      (field_normal x, v) :: arguments_comp lx' lv'
    end
  end.
      

(**************************************************************)
(** ** Definition of the interpreter *)

Coercion ret_result : result >-> ret.

Fixpoint run (max_step : nat) (h0 : heap) (s : scope) (e : expr) : out :=
  match max_step with
  | O => out_bottom
  | S max_step' =>
    let run' := run max_step' in 
    let run_list_value' := run_list_value max_step' in 
    match e with

    | expr_skip =>
      out_return h0 value_undef

    | expr_literal i =>
      out_return h0 (value_of_literal i)

    | expr_var_decl f None =>
      out_return h0 value_undef

    | expr_var_decl f (Some e) =>
      if_success (run' h0 s (expr_assign (expr_variable f) None e)) (fun h1 r1 =>
        out_return h1 value_undef)

    | expr_variable name =>
      let l := scope_comp h0 name s in
        out_return h0 (ret_ref l name)

    | expr_binary_op e1 op e2 =>
      if_success_value (run' h0 s e1) (fun h1 v1 =>
        if_success_value (run' h1 s e2) (fun h2 v2 =>
          if_defined h2 (binary_op_comp op h2 v1 v2) (fun v =>
            out_return h2 v)))

    | expr_and e1 e2 =>
      if_success_value (run' h0 s e1) (fun h1 v1 =>
        if_convert_to_bool h1 v1 (fun _ =>
          if_success_value (run' h1 s e2) (fun h2 v2 =>
            out_return h2 v2))
        (fun _ =>
          out_return h1 v1)) 

    | expr_or e1 e2 =>
      if_success_value (run' h0 s e1) (fun h1 v1 =>
        if_convert_to_bool h1 v1 (fun _ =>
          out_return h1 v1)
        (fun _ =>
          if_success_value (run' h1 s e2) (fun h2 v2 =>
            out_return h2 v2)))

    | expr_unary_op op e =>
      match op with
 
      | unary_op_typeof =>
        if_success (run' h0 s e) (fun h1 r1 =>
         if_is_null_ref r1 (fun _ =>
           out_return h1 (value_string "undefined")
         ) (fun _ =>
          if_defined h1 (getvalue_comp h1 r1) (fun v1 =>
            if_defined h1 (typeof_comp h1 v1) (fun str =>
              out_return h1 (value_string str)))))

     | unary_op_pre_incr | unary_op_pre_decr | unary_op_post_incr | unary_op_post_decr =>
       if_success (run' h0 s e) (fun h1 r1 =>
         if_is_ref h1 r1 (fun l f =>
           if_defined h1 (getvalue_comp h1 r1) (fun v =>
           if_defined h1 (binary_op_comp binary_op_add h0
               match op with
               | unary_op_pre_incr | unary_op_post_incr => (number_of_int 1)
               | unary_op_pre_decr | unary_op_post_decr => (number_of_int (-1)%Z)
               | _ => arbitrary
               end v) (fun va =>
             let vr := match op with
                       | unary_op_pre_incr | unary_op_pre_decr => v
                       | unary_op_post_incr | unary_op_post_decr => va
                       | _ => arbitrary
                       end in
             let h2 := update h1 l f va in
             out_return h2 vr))))

      | unary_op_delete =>
        if_success (run' h0 s e) (fun h1 r =>
          ifb dont_delete r then (
            out_return h1 (value_bool false))
          else (
            let h2 := dealloc h1 r in
            out_return h2 (value_bool true)))
 
      | _ =>
        if_success_value (run' h0 s e) (fun h1 v1 =>
          if_defined h1 (unary_op_comp op h1 v1) (fun v =>
            out_return h1 v))

      end

    | expr_object lxe =>
      (* allocate new object *)
      let l := fresh_for h0 in
      let h1 := alloc_obj h0 l loc_obj_proto in
      let '(lx,le0) := LibList.split lxe in
      (* writing the fields *)
      run_list_value' h1 s nil le0 (fun h2 lv2 =>
              let lfv := arguments_comp lx lv2 in
              let h3 := write_fields h2 l lfv in
              out_return h3 (value_loc l))
      
    | expr_member e1 f =>
      if_success (run' h0 s (expr_access e1 (expr_literal (literal_string f)))) (fun h2 r2 =>
        if_is_ref h2 r2 (fun _ f =>
          if_is_field_normal h2 f (fun _ =>
            out_return h2 r2)))

    | expr_access e1 e2 =>
      if_success (run' h0 s e1) (fun h1 r1 =>
        if_not_eq loc_null h1 (getvalue_comp h1 r1) (fun l =>
          if_success (run' h1 s e2) (fun h2 r2 =>
            if_is_string h2 (getvalue_comp h2 r2) (fun f =>
              out_return h2 (ret_ref l f)))))

    | expr_assign e1 None e2 =>
      if_success (run' h0 s e1) (fun h1 r1 =>
        if_is_ref h1 r1 (fun l f =>
          if_success_value (run' h1 s e2) (fun h2 v =>
            out_return (update h2 l f v) v)))

    | expr_assign e1 (Some op) e2 =>
      if_success (run' h0 s e1) (fun h1 r1 =>
        if_is_ref h1 r1 (fun l f =>
          if_defined h1 (getvalue_comp h1 r1) (fun v1 =>
            if_success_value (run' h1 s e2) (fun h2 v2 =>
              if_defined h2 (binary_op_comp op h2 v1 v2) (fun v =>
                out_return (update h2 l f v) v)))))

    | expr_with e1 e2 =>
      if_success (run' h0 s e1) (fun h1 r1 =>
        if_not_eq loc_null h1 (getvalue_comp h1 r1) (fun l =>
          if_success (run' h1 (l :: s) e2) (fun h2 r2 =>
            out_return h2 r2)))

    | expr_function None f e =>
      let l := fresh_for h0 in
      let h1 := alloc_obj h0 l loc_obj_proto in
      let l' := fresh_for h1 in
      let h2 := alloc_fun h1 l' s f e l in
      out_return h2 (value_loc l')

    | expr_function (Some y) f e =>
      let l := fresh_for h0 in
      let h1 := alloc_obj h0 l loc_obj_proto in
      let l1 := fresh_for h1 in
      let h2 := alloc_obj h1 l1 loc_obj_proto in
      let l' := fresh_for h2 in
      let h3 := alloc_fun h2 l' (l1 :: s) f e l in
      let h4 := write h3 l1 (field_normal y) (value_loc l') in
      out_return h4 (value_loc l')

    | expr_call e1 le2 =>
      if_success (run' h0 s e1) (fun h1 r1 =>
        if_eq loc_eval h1 (getvalue_comp h1 r1) (fun _ =>
          make_error h0 "Not_implemented"
        ) (fun l1 =>
          let l2 := get_this h1 r1 in
          if_binds_scope_body h1 l1 (fun s3 lx e3 =>
            let ys := defs lx e3 in
            run_list_value' h1 s nil le2 (fun h2 lv2 =>
              let l3 := fresh_for h2 in
              let h3 := alloc_obj h2 l3 loc_null in
              let h4 := write h3 l3 field_this l2 in
              let lfv := arguments_comp lx lv2 in
              let h5 := write_fields h4 l3 lfv in
              let h6 := write_fields h5 l3
                (LibList.map (fun y => (field_normal y, value_undef)) ys) in
              if_success_value (run' h6 (l3 :: s3) e3) (fun h7 v3 =>
                out_return h7 v3)))))

    | expr_this =>
      let l1 := scope_comp h0 field_this s in
      let l2 := proto_comp h0 field_this l1 in
      if_binds_field_loc field_this h0 l2 (fun l3 =>
        out_return h0 (value_loc l3))

    | expr_new e1 le2 =>
      (* Evaluate constructor *)
      if_success (run' h0 s e1) (fun h1 r1 =>
        if_not_eq loc_null h1 (getvalue_comp h1 r1) (fun l1 =>
          if_binds_scope_body h1 l1 (fun s3 lx e3 =>
            if_binds_field field_normal_prototype h1 l1 (fun v1 =>
              let l2 := obj_or_glob_of_value v1 in
              (* Evaluate parameters *)
              run_list_value' h1 s nil le2 (fun h2 lv2 =>
                (* Init new object *)
                let l4 := fresh_for h2 in
                let h3 := alloc_obj h2 l4 l2 in
                (* Create activation record *)
                let l3 := fresh_for h3 in
                let ys := defs lx e3 in
                let h4 := write h3 l3 field_proto (value_loc loc_null) in
                let h5 := write h4 l3 field_this (value_loc l4) in
                let lfv := arguments_comp lx lv2 in
                let h6 := write_fields h5 l3 lfv in
                let h7 := reserve_local_vars h6 l3 ys in
                (* Execute function (constructor) body *)
                if_success_value (run' h7 (l3 :: s3) e3) (fun h8 v3 =>
                  let l := obj_of_value v3 l4 in
                  out_return h8 (value_loc l)))))))

    | expr_seq e1 e2 =>
      if_success (run' h0 s e1) (fun h1 r1 =>
        if_success (run' h1 s e2) (fun h2 r2 =>
          out_return h2 r2))

    | expr_if e1 e2 eo =>
      if_success_value (run' h0 s e1) (fun h1 v =>
        if_boolean h1 v (fun _ =>
          run' h1 s e2) (fun _ =>
            match eo with
            | Some e3 =>
              run' h1 s e3
            | None =>
              out_return h1 value_undef
            end))

    | expr_while e1 e2 =>
      if_success_value (run' h0 s e1) (fun h1 v1 =>
        if_boolean h1 v1 (fun _ =>
          if_success (run' h1 s (expr_while e1 e2)) (fun h2 r2 =>
            out_return h2 value_undef))
        (fun _ => out_return h1 value_undef))

    end
  end

with run_list_value (max_step : nat) (h1 : heap) (s : scope)
  (lv : list value) (le0 : list expr) (k : heap -> list value -> out) : out :=
  match max_step with
  | O => out_bottom
  | S max_step' =>
    let run' := run max_step' in
    let run_list_value' := run_list_value max_step' in
    match le0 with
    | nil => k h1 (LibList.rev lv)
    | e::le' =>
      if_success_value (run' h1 s e) (fun h2 v =>
        run_list_value' h2 s (v::lv) le' k)
    end
  end.

End Interpreter.

