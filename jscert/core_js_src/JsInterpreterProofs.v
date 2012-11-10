Set Implicit Arguments.
Require Import Shared.
Require Import LibFix.
Require Import JsSemanticsAux JsWf JsWfAux JsSafety JsScopes JsInterpreter.


(**************************************************************)
(** ** Correctness of proto_comp. *)

Section Proto.

(** Termination of [proto_comp] *)

Inductive proto_closer : binary (heap * field * loc) :=
  | proto_closer_next : forall h f (l l':loc),
      ok_heap h ->
      ~ indom h l f ->
      binds h l field_proto l' ->
      proto_closer (h, f, l') (h, f, l).

Lemma proto_closer_wf : wf proto_closer.
Proof.
  intros [[h f] l]. constructor.
  intros [[h' f'] l'] H. inverts H as O D B1.
  lets~ N: ok_heap_protochain B1. inverts N as B2 P.
    false. forwards*: ok_heap_null B1.
  forwards E: binds_func_loc B2 B1. subst.
  clears O B1 B2 D.
  induction P; constructor; intros [[h2 f2] l2] M; inverts M.
    false. forwards*: ok_heap_null.
    forwards E: binds_func_loc H H8. subst*.
Qed.

Lemma proto_comp_fix : forall h f l, 
  ok_heap h -> proto_comp h f l = proto_comp_body proto_comp h f l.  
Proof.
  applys~ (FixFun3_fix_partial proto_closer). apply proto_closer_wf.
  intros h1 f1 l1 proto_comp1 proto_comp2 O Cont. unfolds.
  repeat case_if*.
    sets_eq v: (read h1 l1 field_proto). destruct~ v.
    applys~ Cont. constructor~. rewrite* binds_equiv_read.
Qed.

(** Correctness and completeness of [proto_comp] *)

Hint Constructors proto.

Lemma proto_comp_correct : forall h f l l',
  ok_heap h ->
  bound h l ->
  proto_comp h f l = l' -> 
  proto h f l l'.
Proof.
  introv OK B E. forwards~ PC: ok_heap_protochain_bound B.
  induction PC.
   lets (f'&B1): B. rewrite indom_equiv_binds in B1.
    lets (v&B2): B1. forwards*: ok_heap_null B2.
   rewrite~ proto_comp_fix in E.
    unfold proto_comp_body in E.
    case_if*. subst~.
    case_if*. subst~.
    case_if* in E.
     rewrite~ binds_equiv_read in H.
      rewrite H in E. rewrite* <- binds_equiv_read in H.
      apply* proto_next.
      tests: (l'0 = loc_null).
        rewrite~ proto_comp_fix in E.
         unfolds in E. case_if. subst~.
        apply* IHPC. inverts* PC. apply* binds_bound.
   false n1.
    lets (v&B1): B. rewrite indom_equiv_binds in B1.
    lets (v'&B2): B1. forwards~ B3: ok_heap_protochain B2.
    inverts* B3. rewrite* indom_equiv_binds.
Qed.

Lemma proto_comp_complete : forall h f l l',
  ok_heap h ->
  bound h l ->
  proto h f l l' ->
  proto_comp h f l = l'.
Proof.
  introv OK B P. induction P; 
   rewrite* proto_comp_fix; unfold proto_comp_body; case_if*.
  case_if*.
  subst. lets (f'&B'): B. rewrite~ indom_equiv_binds in B'.
   lets (v&B''): B'. forwards*: ok_heap_null B''.
  case_if*. case_if*. 
    rewrite (binds_read H0).
     tests: (l' = loc_null).
       asserts: (l'' = loc_null).
         apply* proto_func.
       subst. rewrite* proto_comp_fix. unfold proto_comp_body. case_if*.
      apply* IHP.
       forwards*: ok_heap_ok_value H0.
       inverts* H1. inverts* H2. apply* indom_bound.
    false n1. rewrite* indom_equiv_binds.
Qed.

End Proto.


(**************************************************************)
(** ** Correctness of scope_comp. *)

Section Scopes.

(** Correctness and completeness of [scope_comp] *)

Lemma scope_comp_correct : forall h f L l',
  scope_comp h f L = l' ->
  ok_heap h ->
  ok_scope h L ->
  scopes h f L l'.
Proof.
  introv E OK OKL.
  lets~ FOK: ok_scope_all_bound (rm OKL) OK.
  gen h f L l'. induction L; introv OKL E.
  inverts E. constructor*. 
  simpls. inverts OKL as (Ba & BL).
  lets* (l&Hl): proto_defined h f a. apply* indom_bound.
  assert (forall l', proto_comp h f a = l' -> l = l').
    introv E'. lets*: proto_comp_correct E'.
      apply* indom_bound.
      apply* proto_func.
  forwards: (rm H); [ reflexivity | ]. subst. case_if*.
    constructor*.
     apply* proto_comp_correct.
     apply* indom_bound.
    apply* scopes_here.
Qed.

Lemma scope_comp_complete : forall h f L l',
  scopes h f L l' ->
  ok_heap h ->
  ok_scope h L ->
  scope_comp h f L = l'.
Proof.
  introv Sc OK OKL. forwards~ FOK: ok_scope_all_bound (rm OKL).
  induction Sc; simpls*.
  asserts Eq: (proto_comp h f l = l').
    forwards*: proto_comp_complete H. inverts* H.
      apply* indom_bound.
      apply* binds_bound.
   inverts FOK. rewrite Eq. forwards*: proto_comp_correct Eq. case_if*.
  inverts FOK. case_if*. false. lets*: proto_comp_complete H.
  (* LATER: use [case_if* as C] *)
Qed.

End Scopes.


(**************************************************************)
(** ** Correctness of getvalue_comp. *)

Section Getvalue.

(** Correctness and completness of [getvalue_comp] *)

Lemma getvalue_comp_correct_ref : forall h l f v,
  getvalue_comp h (Ref l (field_normal f)) = Some v ->
  ok_heap h ->
  bound h l ->
  getvalue h (Ref l (field_normal f)) v.
Proof.
  introv E OK B. unfolds in E. case_if*.
  asserts [l' Hl']: (exists l', proto_comp h (field_normal f) l = l').
    destruct* proto_comp. 
  rewrite Hl' in E. case_if*; inverts~ E.
    apply* getvalue_ref_null. subst. apply* proto_comp_correct.
    lets~ M: proto_comp_correct Hl'. applys* getvalue_ref_not_null.
      applys~ read_binds. apply* proto_indom.
Qed.

Lemma getvalue_comp_correct : forall h r v,
  getvalue_comp h r = Some v ->
  ok_result h r ->
  ok_heap h ->
  getvalue h r v.
Proof.
  introv E R OK. unfolds getvalue_comp.
  destruct r as [|[l f]].
    inverts E. constructor.
    asserts [f' Hf]: (exists f', f = field_normal f').
      destruct* f; false.
     subst. apply* getvalue_comp_correct_ref. case_if*.
      inverts R as R. inverts* R.
      apply* indom_bound.
Qed.

Lemma getvalue_comp_complete : forall h r v,
  getvalue h r v ->
  ok_heap h ->
  getvalue_comp h r = Some v.
Proof.
  introv Gv OK. unfold getvalue_comp. induction Gv.
  fequals.
  case_if*. forwards* M: proto_comp_complete H.
    inverts H; tryfalse. apply* binds_bound. applys* binds_bound.
   rewrite M. case_if*. fequals. applys* binds_read.
  case_if*. forwards*: proto_comp_complete H. (* ARTHUR: can you factorize the pattern with the other case? *)
    inverts H; tryfalse. apply* binds_bound.
   case_if*.
Qed.

End Getvalue.


(**************************************************************)
(** ** Lemmas for the correctness of the interpreter *)

Section Correctness.

Global Instance out_comparable : Comparable out.
Proof.
  (* Warning: This proof is classical, and is only there for the proofs.
      It shouldn't be extracted. *)
  (* TODO: do we want/need a version that can be extracted? *)
      (* Martin: I don't thing so for this case: I'm just using it to apply the lemmas `elim_*'. *)
  applys (@comparable_beq out) (fun (o1 o2 : out) =>
    If o1 = o2 then true else false). (* todo: remove type annot *)
  split; introv E.
   case_if*.
   subst; case_if*.
Qed.

Lemma wrong_not_ret : forall h h' r,
  wrong h <> out_return h' (ret_result r).
Proof.
  introv. unfold wrong.
  destruct Mnostuck; discriminate.
Qed.

Lemma ret_not_wrong : forall h h' r,
  out_return h' (ret_result r) <> wrong h.
Proof. introv E. symmetry in E. forwards*: wrong_not_ret E. Qed.

Lemma elim_if_success : forall r0 k h r,
  if_success r0 k = out_return h r ->
  (r0 = out_return h r /\ forall v, r <> ret_result v) \/
    exists r1 h0, r0 = out_return h0 (ret_result r1).
Proof.
  introv E. destruct r0.
   destruct* r0. inverts E. left. split*. introv. discriminate.
   simpls. inverts* E.
   simpls. inverts* E.
Qed.

Lemma elim_if_defined : forall A h f r (a : option A),
  if_defined h a f = r ->
  a = None \/ exists b, a = Some b.
Proof. introv E. destruct* a. Qed.

Lemma elim_if_success_value : forall r0 k h r,
  if_success_value r0 k = out_return h r ->
  (r0 = out_return h r /\ forall v, r <> ret_result v) \/
  (exists v h, r0 = out_return h (ret_result v) /\ getvalue_comp h v = None) \/
  exists v h b, r0 = out_return h (ret_result v) /\ getvalue_comp h v = Some b.
Proof.
  introv E.
  unfolds in E.
  forwards~ [OK | (v&h'&E')]: elim_if_success E.
  right. subst. simpls.
  forwards~ [? | ?]: elim_if_defined E.
  rewrite H in E. simpls.
   left*.
  lets (b&E'): H. right*.
Qed.

Lemma elim_if_is_ref : forall h o k r,
  if_is_ref h o k = r ->
  ((exists h', wrong h' = r) /\ exists v, o = result_value v)
    \/ exists l f, o = result_ref (Ref l f).
Proof.
  introv E. destruct* o.
  inverts E. right. destruct* r0.
Qed.

Lemma elim_if_is_null_ref : forall r k1 k2 rf,
  if_is_null_ref r k1 k2 = rf ->
  (exists v, r = result_value v) \/
  (exists l f, l <> loc_null /\ r = Ref l f /\ rf = k2 r) \/
  exists f, r = Ref loc_null f /\ rf = k1 f.
Proof.
  introv E. destruct r.
   left*.
   right. destruct r. simpl in E.
    case_if.
     subst*.
     left*.
Qed.

Lemma elim_if_is_field_normal : forall h f k r,
  if_is_field_normal h f k = r ->
  (r = wrong h) \/ exists f', f = field_normal f'.
Proof. introv E. destruct f; simpls*. Qed.

Lemma elim_if_eq : forall l0 h o k1 k2 r,
  if_eq l0 h o k1 k2 = r ->
  o = None \/
  (exists v, o = Some v /\ r = wrong h) \/
  (o = Some (value_loc l0) /\ r = k1 I) \/
  exists l, o = Some (value_loc l) /\ l <> l0 /\ r = k2 l.
Proof.
  introv E. destruct* o.
  right. destruct v; inverts* E.
  right. tests: (l0 = l).
   left. split~. simpl. case_if*.
   right. exists l. splits~. simpl. case_if*.
Qed.

Lemma elim_if_not_eq : forall l0 h o k r,
  if_not_eq l0 h o k = r ->
  o = None \/
    ((exists h', wrong h' = r) /\ exists v, o = Some v) \/
    exists l, o = Some (value_loc l) /\ l <> l0.
Proof.
  introv E.
  forwards* [eqr | [(v&eqo&eqr) | [(eqo&eqr) | (l&eqo&_&eqr)]]]: elim_if_eq E.
  substs. simpls.
  case_if.
   branch 2. splits*.
   branch 3. exists l. split~.
Qed.

Lemma elim_if_is_string : forall h o k r,
  if_is_string h o k = r ->
  o = None \/
    ((exists h', wrong h' = r) /\ exists v, o = Some v) \/
    exists s, o = Some (value_string s).
Proof. introv E. destruct* o. right. destruct v; inverts* E. Qed.

Lemma elim_if_binds_field : forall f h l k r,
  if_binds_field f h l k = r ->
  (r = wrong h /\ ~indom h l f) \/
  (exists v, r = k v /\ binds h l f v).
Proof.
  introv E.
  unfolds in E. case_if* in E.
  right. eexists. split*.
  rewrite* binds_equiv_read.
Qed.

Lemma elim_if_binds_field_loc : forall f h l k r,
  if_binds_field_loc f h l k = r ->
  (r = wrong h /\ forall l', ~binds h l f (value_loc l')) \/
  (exists l', r = k l' /\ binds h l f (value_loc l')).
Proof.
  introv E. unfolds in E.
  lets* [C1 | C2]: elim_if_binds_field E.
  lets (H&H0): C1. left. split~. introv B.
    false H0. rewrite* indom_equiv_binds.
  lets (v&R&B): C2.
   destruct v; try (
     left; split~; introv B';
     forwards~ H: binds_func B B'; discriminate H).
   right. exists l0. split~.
Qed.

Lemma elim_if_boolean : forall h v k1 k2 r,
  if_boolean h v k1 k2 = r ->
  (r = wrong h /\ forall b, v <> value_bool b) \/
  (r = k1 I /\ v = value_bool true) \/
  (r = k2 I /\ v = value_bool false).
Proof.
  introv E. destruct v; simpls;
    try (left; subst; split; [reflexivity | discriminate]).
  right. destruct b; [left* | right*].
Qed.

Lemma elim_if_binds_scope_body : forall h l k r,
  if_binds_scope_body h l k = r ->
  r = wrong h \/
  (indom h l field_body /\
    indom h l field_scope /\
    exists s f e, read h l field_scope = value_scope s /\
    read h l field_body = value_body f e /\ k s f e = r).
Proof.
  introv E. unfold if_binds_scope_body in E.
  lets* [C1 | C2]: elim_if_binds_field E.
  lets (v&R&B): C2. clear C2.
  destruct v; try (left~; fail).
  symmetry in R. lets* [C1 | C2]: elim_if_binds_field R.
  lets (v&R'&B'): C2. clear C2.
  destruct v; try (left~; fail).
  right. splits; try rewrite* indom_equiv_binds.
  repeat eexists; eauto; rewrite* <- binds_equiv_read; rewrite* indom_equiv_binds.
Qed.

Lemma sub_safety : forall h h' s e r,
    red h s e h' r -> ok_heap h -> ok_scope h s ->
    ok_heap h' /\ ok_scope h' s /\ ok_result h' r.
Proof. intros. splits; apply* safety. Qed.

Lemma arguments_comp_correct : forall xs vs lfv,
  arguments_comp xs vs = lfv ->
  arguments xs vs lfv.
Proof.
  induction xs; introv E.
   simpls. subst. constructors.
   destruct vs.
     simpls. rewrite <- E. apply* arguments_nil_values.
     simpls. rewrite <- E. apply* arguments_cons.
Qed.


(**************************************************************)
(** ** Tactics for the correctness of the interpreter *)

Ltac name_heap_write h' :=
  match goal with  |- context [ write ?h ?l ?f ?v ] =>
    sets_eq h': (write h l f v) end.
Ltac name_heap_sub_write h' :=
  match goal with  |- context [ write (write ?h ?l ?f ?v) _ _ _ ] =>
    sets_eq h': (write h l f v) end.
Ltac name_heap_write_fields h' :=
  match goal with  |- context [ write_fields ?h ?l ?li ] =>
    sets_eq h': (write_fields h l li) end.
Ltac name_heap_reserve_local_vars h' :=
  match goal with  |- context [ reserve_local_vars ?h ?l ?li ] =>
    sets_eq h': (reserve_local_vars h l li) end.
Ltac name_heap_alloc_obj H h' :=
  match goal with |- context [ alloc_obj ?h ?l ?l' ] =>
    sets_eq h': (alloc_obj h l l') end.
Ltac name_heap_write_in H h' :=
  match goal with  H: context [ write ?h ?l ?f ?v ] |- _ =>
    sets_eq h': (write h l f v) end.
Ltac name_heap_sub_write_in H h' :=
  match goal with  H: context [ write (write ?h ?l ?f ?v) _ _ _ ] |- _ =>
    sets_eq h': (write h l f v) end.
Ltac name_heap_write_fields_in H h' :=
  match goal with  H: context [ write_fields ?h ?l ?li ] |- _ =>
    sets_eq h': (write_fields h l li) end.
Ltac name_heap_sub_write_fields_in H h' :=
  match goal with  H: context [ write_fields (write_fields ?h ?l ?li) _ _ ] |- _ =>
    sets_eq h': (write_fields h l li) end.
Ltac name_heap_reserve_local_vars_in H h' :=
  match goal with  H: context [ reserve_local_vars ?h ?l ?li ] |- _ =>
    sets_eq h': (reserve_local_vars h l li) end.
Ltac name_heap_alloc_obj_in H h' :=
  match goal with  H: context [ alloc_obj ?h ?l ?l' ] |- _ =>
    sets_eq h': (alloc_obj h l l') end.


(**************************************************************)
(** ** Correctness of the implementation of operators *)

Lemma typeof_comp_correct : forall h v str,
  typeof_comp h v = Some str ->
  ok_heap h ->
  typeof_red h v str.
Proof.
  introv E OK.
  destruct v; try (inverts E; constructor).
  simpl in E. case_if; inverts E.
   rewrite indom_equiv_binds in i. lets (v&B): i.
    apply* typeof_red_function. exists* v.
   lets OKf: ok_heap_function OK. unfolds in OKf.
   apply* typeof_red_object. introv (v&B). false n.
    forwards (?&?&?&?&F&?&?): OKf B.
    rewrite* indom_equiv_binds.
Qed.

Inductive proto_closer_for_binary_op_comp : binary (binary_op * heap * value * value) :=
  | proto_closer_for_binary_op_comp_instanceof : forall h (l1 l2 l3 l4:loc),
      ok_heap h ->
      binds h l1 field_normal_prototype (value_loc l3) ->
      binds h l2 field_proto (value_loc l4) ->
      l3 <> l4 ->
      proto_closer_for_binary_op_comp (binary_op_instanceof, h, value_loc l1, value_loc l4) (binary_op_instanceof, h, value_loc l1, value_loc l2).

Lemma proto_closer_for_binary_op_comp_wf : wf proto_closer_for_binary_op_comp.
Proof.
  intros [[[b h] v1] v2]. constructor.
  intros [[[b' h'] v1'] v2'] H. inverts H as O B1 B2 D.
  lets~ N: ok_heap_protochain B2. inverts N as B3 P.
    false. forwards*: ok_heap_null B2.
  forwards*: binds_func_loc B3 B2. subst.
  clears O B1 B2 B3 D.
  induction P; constructor; intros [[[b'' h''] v1''] v2''] M; inverts M.
    false. forwards*: ok_heap_null.
    forwards E: binds_func_loc H H9. subst*.
Qed.

Lemma binary_op_comp_fix : forall h op v1 v2,
  ok_heap h -> binary_op_comp op h v1 v2 = binary_op_comp_body binary_op_comp op h v1 v2.
Proof.
  introv O. applys~ (FixFun4_fix_partial proto_closer_for_binary_op_comp (fun _ h _ _ => ok_heap h)).
    apply proto_closer_for_binary_op_comp_wf.
  introv O1 Cont. unfolds. destruct~ x1.
    repeat case_if~. destruct~ x3. simpl. destruct~ x4.
    case_if~; symmetry; case_if~.
    sets_eq v: (read x2 l field_normal_prototype). destruct~ v.
    sets_eq v: (read x2 l0 field_proto). destruct~ v.
    simpls. repeat case_if~.
    rewrite~ Cont.
    apply~ proto_closer_for_binary_op_comp_instanceof.
      rewrite* binds_equiv_read.
      rewrite* binds_equiv_read.
      auto*.
Qed.

Lemma binary_op_comp_correct : forall b h v1 v2 r,
  binary_op_comp b h v1 v2 = Some r ->
  ok_heap h -> ok_value h v1 -> ok_value h v2 ->
  binary_op_red b h v1 v2 r.
Proof.
  introv E OK O1 O2. rewrite~ binary_op_comp_fix in E.
  destruct b; simpls.
  (* add *)
  destruct v1; destruct v2; simpls; tryfalse.
    inverts E. constructor*.
    inverts E. constructor*.
  (* mult *)
  destruct v1; destruct v2; simpls; tryfalse.
   inverts E. constructor*.
  (* div *)
  destruct v1; destruct v2; simpls; tryfalse.
   inverts E. constructor*.
  (* equal *)
  case_if in E as B; tryfalse. lets (B1&B2): a. inverts~ E.
  rewrite~ value_compare_correct. constructor~.
  
  (* instanceof *)
  destruct v1; simpls; tryfalse.
  apply* binary_op_red_instanceof.
  case_if in E.
   inverts E. apply* instanceof_red_value.
   inverts* O2.
    unfolds in H. rewrite~ indom_equiv_binds in H.
    lets (v0 & B): (rm H).
    lets~ N: ok_heap_protochain B.
    clear n v0 B. induction N.
     false. case_if in E.
      set_eq v: (read h l field_normal_prototype) in E.
      destruct v; tryfalse. simpl in E. case_if in E.
      rewrite~ indom_equiv_binds in i0. lets (v & B): i0.
      forwards*: ok_heap_null B.
     gen E; intro E. case_if in E. (* FIXME: It seems there is a bug in `case_if' that make it ignore what stands after a `in' argument. *)
      set_eq v: (read h l field_normal_prototype) in E.
      destruct v; simpls; tryfalse. case_if in E.
      set_eq v: (read h l0 field_proto) in E.
      destruct v; simpls; tryfalse.
      asserts: (l2 = l').
        applys~ binds_func_loc H.
        rewrite* binds_equiv_read.       
      subst l'. case_if in E.
       inverts E. subst. apply* instanceof_red_true.
         rewrite* binds_equiv_read.
       apply* instanceof_red_trans.
         rewrite* binds_equiv_read.
        tests: (l2 = loc_null).
          clear IHN. rewrite~ binary_op_comp_fix in E.
           simpl in E. case_if in E.
            inverts E. constructor~.
            false n0. constructor.
          apply* IHN; clear IHN.
           rewrite~ binary_op_comp_fix in E.
           simpl in E. case_if in E.
            false. inverts~ b.
            apply* E.

  (* in *)
  destruct v1; destruct v2; simpls; tryfalse. inverts E.
  inverts O2.
   inverts H.
    apply* binary_op_red_in.
      constructor.
    case_if.
     rewrite~ proto_comp_fix. unfold proto_comp_body.
     case_if. rewrite decide_spec. fold_bool. apply* eqb_eq.
   apply* binary_op_red_in.
     apply* proto_comp_correct.
      apply* indom_bound.
     rewrite decide_spec. case_if*.
      rewrite* eqb_eq.
      rewrite* eqb_neq.
Qed.

Lemma unary_op_comp_correct : forall b h v r,
  unary_op_comp b h v = Some r ->
  unary_op_red b h v r.
Proof.
  introv E.
  destruct b; simpls; tryfalse.

  (* not *)
  destruct v; tryfalse.
  inverts~ E. apply* unary_op_red_not.

  (* void *)
  inverts~ E. apply* unary_op_red_void.
Qed.


(**************************************************************)
(** ** Correctness of the interpreter *)

Lemma run_list_value_add_value : forall m s h0 es vs vs0 k k' r,
  run_list_value m h0 s (vs ++ vs0) es k = r ->
  (forall h vs', k' h vs' = k h (LibList.rev vs0 ++ vs')) ->
  run_list_value m h0 s vs es k' = r.
Proof.
  induction m.
    simpl. intros; subst~.
    introv E T. destruct es; simpls.
     rewrite <- E. rewrite rev_app. apply* T.
    destruct~ run. destruct~ r0. simpls.
     destruct~ getvalue_comp. simpls. apply* IHm.
Qed.

Theorem run_correct : forall m h s e h' v,
  run m h s e = out_return h' (ret_result v) ->
  ok_heap h ->
  ok_scope h s ->
  red h s e h' v
with run_list_value_correct : forall m h1 s es k h3 v,
  run_list_value m h1 s nil es k = out_return h3 (ret_result v) ->
  ok_heap h1 ->
  ok_scope h1 s ->
  exists h2 vs,
  k h2 vs = out_return h3 (ret_result v) /\
  red_list_value h1 s es h2 vs.
Proof.
  intro m. destruct m.
    introv R OK OKL; false.
  destruct e; introv R OK OKL; simpl in R;
    try (inverts* R; fail).

  (* this *)
  forwards [(?&_) | (l'&eq&B)]: elim_if_binds_field_loc R.
    forwards*: ret_not_wrong H.
  inverts* eq.
  apply* red_this.
    apply* scope_comp_correct.
  apply* proto_comp_correct.
  sets_eq ls: (scope_comp h field_this s).
  symmetry in EQls. forwards* Pro: scope_comp_correct EQls.
  inverts Pro.
    rewrite <- H in B.
    rewrite* proto_comp_fix in B.
    unfold proto_comp_body in B. case_if~ in B.
    forwards*: ok_heap_null B.
  inverts keep H; tryfalse.
    exists~ field_this.
    apply* binds_bound.
  asserts (lp&Dlp&Plp): (exists l', l' <> loc_null /\ proto h field_this ls l').
    apply* scopes_proto_not_null.
    intro_subst.
    rewrite* proto_comp_fix in B.
    unfold proto_comp_body in B. case_if~ in B.
    forwards*: ok_heap_null B.
  inverts* Plp.
    exists~ field_this.
  apply* binds_bound.

  (* variable *)
  inverts* R.
  apply red_variable.
  apply* scope_comp_correct.

  (* literal *)
  inverts* R. constructor*.

  (* obj *)
  name_heap_alloc_obj_in R h3.
  sets_eq sl: (split l). destruct sl as [lx lx0].
  asserts OK3: (ok_heap h3).
    subst h3. apply* ok_heap_alloc_obj.
      apply* ok_heap_protochain_indom. applys* ok_heap_special_obj_proto OK.
      right. applys* ok_heap_special_obj_proto OK.
      apply fresh_for_spec.
  asserts OKL3: (ok_scope h3 s).
    applys* ok_scope_extends h.
    subst h3. apply* extends_proto_write.
  forwards~ (h2&vs&R'&IHR): run_list_value_correct R.
  inverts R'.
  apply* red_object.
    apply* fresh_for_spec.
    rewrite <- EQh3. apply IHR.
    apply* arguments_comp_correct.

  (* functions *)
  destruct o.
    (* --named *)
    inverts R.
    apply* red_function_named; apply* fresh_for_spec.
    (* --unnamed *)
    inverts R.
    apply* red_function_unnamed; apply* fresh_for_spec.

  (* access *)
  forwards [(?&?) | (r1&h1&eq1)]: elim_if_success R; tryfalse.
  rewrite eq1 in R. simpl in R.
  forwards  [eqr | [(eqr&v'&eqo) | (l&eqo&diffno)]]: elim_if_not_eq R.
    rewrite eqr in R. simpl in R. forwards*: wrong_not_ret R.
    lets (h'0&eqr'): eqr. forwards*: wrong_not_ret eqr'.
  rewrite eqo in R. simpl in R.
  case_if* in R; tryfalse.
  forwards [(?&?) | (r2&h2&eq2)]: elim_if_success R; tryfalse.
  rewrite eq2 in R. simpl in R.
  forwards [eqr2 | [(eqr2&v''&eqr2') | (str&eqstr)]]: elim_if_is_string R.
    rewrite eqr2 in R. simpl in R. forwards*: wrong_not_ret R.
    lets (h'0&eqr2''): eqr2. forwards*: wrong_not_ret eqr2''.
  rewrite eqstr in R; simpl in R.
  inverts* R.
  forwards* R1: run_correct eq1.
  forwards* (OK1&OKL1&OKr1): sub_safety R1.
  forwards* R2: run_correct eq2.
  apply* red_access; try apply* getvalue_comp_correct; apply* safety.

  (* member *)
  forwards [(?&?) | (r1&h1&eq1)]: elim_if_success R; tryfalse.
  rewrite eq1 in R; simpl in R.
  forwards [((?&?)&(?&?)) | (l&f&eq2)]: elim_if_is_ref R.
    rewrite H0 in R. simpl in R. forwards*: wrong_not_ret R.
  rewrite eq2 in R. simpl in R.
  forwards [? | (f'&eq3)]: elim_if_is_field_normal R.
    false* wrong_not_ret.
  rewrite eq3 in R. simpl in R.
  subst. inverts* R.
  forwards~ R1: run_correct eq1.
  assert (f' = s0); subst.
    inverts R1. inverts H9. inverts* H10.
  apply* red_member.

  (* new *)
  forwards [(?&?) | (r1&h1&eq1)]: elim_if_success R; tryfalse.
  rewrite eq1 in R. simpl in R.
  forwards [eqr | [((h2&eqr)&(v'&eqo)) | (l1&eqo&diffno)]]: elim_if_not_eq R.
    rewrite eqr in R. simpl in R. forwards*: wrong_not_ret R.
    forwards*: wrong_not_ret eqr.
  rewrite eqo in R; simpl in R.
  case_if* in R.
  forwards* [? | (Ib&Is&sc&f&e2&Escope&Ebody&R')]: elim_if_binds_scope_body R.
    subst. forwards*: ret_not_wrong H.
  clear R. rename R' into R.
  forwards [(?&?) | (v'&R'&Bv')]: elim_if_binds_field R.
    forwards*: ret_not_wrong H.
  clear R. symmetry in R'. rename R' into R.
  forwards* R1: run_correct eq1.
  forwards* (OK1&OKL1&OKr1&Ext1): safety R1.
  forwards~ (h2&vs&R'&IHR): run_list_value_correct R.
  clear R. rename R' into R.
  forwards [(?&?) | [(?&h0&eq3&eqv1) | (?&h0&v1&eq3&eqv1)]]: elim_if_success_value R; tryfalse.
    rewrite eq3 in R. simpls. rewrite eqv1 in R. simpls. forwards*: wrong_not_ret R.
  name_heap_reserve_local_vars_in eq3 h7.
  name_heap_write_fields_in EQh7 h6.
  name_heap_write_in EQh6 h5.
  name_heap_sub_write_in EQh5 h4.
  name_heap_alloc_obj_in EQh4 h3.
  rewrite eq3 in R. simpls. rewrite eqv1 in R. simpls.
  inverts R.
  forwards* (OK2&OKL2&OKlv2&Ext2): safety_list IHR.
  (* What follows is nearly a copy/paste of the corresponding proof in JsSafety. *)
  asserts O3: (ok_heap h3). subst h3. apply* ok_heap_alloc_obj. 
    applys* obj_or_glob_of_value_protochain h1 l1 field_normal_prototype v'.
    right. forwards~: ok_heap_special_obj_proto h1. apply* OK1.
     forwards [(l3&El3)|?]: (value_loc_or_not v'). 
       subst v'. simpl. forwards OV: ok_heap_ok_value OK1.
        unfolds in OV. forwards~: OV Bv'. case_if*.
       rewrite~ obj_or_glob_of_value_not_loc.
       apply* fresh_for_spec.
  asserts S3: (ok_scope h3 s). subst h3. apply* ok_scope_write.
  asserts O4: (ok_heap h4). subst h4. apply* ok_heap_alloc_obj.
    constructor. apply* fresh_for_spec.
  asserts S4: (ok_scope h4 s). subst h4. apply* ok_scope_write.
  asserts O5: (ok_heap h5). subst h5. forwards*: ok_heap_write_this h4 (fresh_for h3) (fresh_for h2).
    subst h4. apply* binds_write_neq. apply* binds_write_eq.
    apply* fresh_for_spec.
    applys neq_sym. applys~ fresh_binds_neq h3. apply* fresh_for_spec.
     applys~ ok_heap_special_global_this. apply* O3.
    subst h4 h3. do 2 apply* indom_write. apply* indom_write_eq.
  asserts S5: (ok_scope h5 s). subst h5. apply* ok_scope_write.
  asserts O6: (ok_heap h6). subst h6. apply* ok_heap_write_fields_user.
    subst h5 h4 h3. apply* indom_write. indom_simpl.
    apply* fresh_for_spec.
    apply* arguments_ok_value.
     apply* arguments_comp_correct.
     applys~ Forall_trans value (ok_value h2).
     introv Oa. applys~ ok_value_extends h2.
     subst h5 h4 h3. repeat apply* extends_proto_write_trans.
  asserts S6: (ok_scope h6 s). subst h6. apply* ok_scope_write_fields.
  asserts O7: (ok_heap h7). subst h7. apply* ok_heap_write_fields_user_undef.
    subst h6 h5 h4. apply* indom_write_fields. apply* indom_write. apply* indom_write_eq.
    apply* fresh_for_spec.
  asserts S7: (ok_scope h7 s). applys* ok_scope_extends.
    subst h7. apply* extends_proto_write_fields_trans.
  assert (ok_scope h7 (fresh_for h3 :: sc)).
    subst h7. apply* ok_scope_write_fields.
    subst h6. apply* ok_scope_write_fields.
    subst h5. apply* ok_scope_write.
    subst h4. apply* ok_scope_cons.
    subst h3. repeat apply* ok_scope_write.
    forwards~ Of: ok_heap_function OK1.
    unfolds in Of.
    rewrite* <- binds_equiv_read in Escope.
    forwards: Of l1.
      left. apply Escope.
    applys* ok_scope_extends h1.
    apply* ok_heap_binds_ok_scope.
    apply* indom_write_eq.
  forwards~ R2: run_correct eq3.
  forwards* (O'&S'&OKr2&E'): safety R2.
  apply* red_new.
    apply* getvalue_comp_correct.
    rewrite* binds_equiv_read.
    rewrite* binds_equiv_read.
    apply* fresh_for_spec.
    apply* fresh_for_spec.
    apply* arguments_comp_correct.
    subst*.
    apply* getvalue_comp_correct.

  (* call *)
  forwards [(?&?) | (r1&h1&eq1)]: elim_if_success R; tryfalse.
  rewrite eq1 in R. simpl in R.
  forwards* [eqr | [(v1&eqo&eqr) | [(eqo&eqr) | (l1&eqo&notEval&eqr)]]]: elim_if_eq R.
    rewrite eqr in R. simpl in R. forwards*: wrong_not_ret R.
    forwards*: ret_not_wrong eqr.
  (* --call to eval *)
  unfold make_error in eqr. inverts* eqr.
  (* -- call to function *)
  clears R. symmetry in eqr. rename eqr into R.
  forwards* [? | (Ib&Is&sc&f&e2&Escope&Ebody&R')]: elim_if_binds_scope_body R.
    subst. forwards*: ret_not_wrong H.
  clear R. rename R' into R.
  forwards* R1: run_correct eq1.
  forwards* (OK1&OKL1&OKr1&Ext1): safety R1.
  forwards~ (h2&vs&R'&IHR): run_list_value_correct R.
  clears R. rename R' into R.
  forwards [(?&?) | [(r2&h3&eq2&eqv0) | (r2&h3&v2&eq2&eqv0)]]: elim_if_success_value R; tryfalse.
    rewrite eq2 in R. simpls. rewrite eqv0 in R. simpls. forwards*: wrong_not_ret R.
  rewrite eq2 in R. simpls. rewrite eqv0 in R. simpls.
  inverts* R.
  forwards* (OK2&OKL2&OKlv2&Ext2): safety_list IHR.
  name_heap_write_fields_in eq2 h6.
  asserts OK2sc: (ok_scope h2 sc).
    lets Of: ok_heap_function OK1. unfolds in Of.
    rewrite* <- binds_equiv_read in Escope.
    forwards: Of l1.
      left. apply Escope.
    applys* ok_scope_extends h1.
    apply* ok_heap_binds_ok_scope.
  name_heap_sub_write_fields_in EQh6 h5.
  name_heap_write_in EQh5 h4.
  name_heap_alloc_obj_in EQh4 h3.
  asserts OK6: (ok_heap h6).
    (* This part is very closed to the corresponding one in JsSafety:
       maybe it can be factorized?*)
    asserts: (has_some_proto h3 (fresh_for h2)). subst h3. indom_simpl.
     subst h6. apply* ok_heap_write_fields_user_undef.
       subst h5 h4 h3. apply~ indom_write_fields. indom_simpl.
       apply* fresh_for_spec.
     subst h5. apply* ok_heap_write_fields_user.
       subst h4 h3. indom_simpl.
       apply* fresh_for_spec.
     subst h4. applys ok_heap_write_this h3 (fresh_for h2) (get_this h1 r1) (@eq_refl). 
       subst h3. apply* ok_heap_alloc_obj. constructor.
       apply* fresh_for_spec.
       subst h3. apply* binds_write_neq. apply* binds_write_eq.
       apply* fresh_for_spec.
       applys neq_sym. applys~ fresh_binds_neq h2. apply* fresh_for_spec.
       applys~ ok_heap_special_global_this. apply* OK2.
       auto.
     destruct r1 as [v1|[l0 f0]].
       subst h3. do 2 apply* indom_write. 
        apply* ok_heap_special_global_proto. apply* OK2.
       unfold get_this. case_if.
         subst h3. do 2 apply* indom_write. 
          apply* ok_heap_special_global_proto. apply* OK2.
         subst h3.
          do 2 apply* has_some_proto_write. inverts OKr1 as [N|P].
            subst l0. simpl in eqo. case_if in eqo.
            forwards~: extends_proto_elim Ext2 P.
     apply* arguments_ok_value. apply* arguments_comp_correct.
     applys~ Forall_trans value (ok_value h2).
       introv Oa. applys~ ok_value_extends h2.
        subst h4 h3. repeat apply* extends_proto_write_trans.
  asserts OKL6: (ok_scope h6 (fresh_for h2 :: sc)).
    subst h6. apply* ok_scope_write_fields.
    subst h5. apply* ok_scope_write_fields.
    subst h4. apply* ok_scope_write.
    subst h3. apply* ok_scope_cons.
    apply* ok_scope_write.
    apply* indom_write_eq.
  forwards* R2: run_correct eq2.
  forwards* (_&OKL'&OKr2&Ext6): safety R2.
  apply* red_call.
    apply* getvalue_comp_correct.
    rewrite* binds_equiv_read.
    rewrite* binds_equiv_read.
    apply* fresh_for_spec.
    apply* arguments_comp_correct.
    rewrite <- EQh3. rewrite <- EQh4. rewrite <- EQh5.
    unfold reserve_local_vars. rewrite <- EQh6.
      apply* R2.
    apply* getvalue_comp_correct.
      apply* safety.

  (* unary_op *)
  destruct u.
  (* not *)
  forwards [(?&?) | [(v0&h1&eq1&eqv0) | (v0&h1&b'&eq1&eqv0)]]: elim_if_success_value R; tryfalse.
    rewrite eq1 in R. simpls. rewrite eqv0 in R. simpls. forwards*: wrong_not_ret R.
  rewrite eq1 in R. simpls. rewrite eqv0 in R. simpls.
  forwards [? | (v2&eqv2)]: elim_if_defined R.
    rewrite H in R; simpl in R; forwards*: wrong_not_ret R.
  rewrite eqv2 in R; simpl in R.
  destruct b'; tryfalse. inverts eqv2.
  inverts~ R.
  forwards~ R': run_correct eq1.
  forwards* (OK1&OKL1&OKr1): sub_safety R'.
  apply* red_unary_op.
    apply* getvalue_comp_correct.
    apply* unary_op_comp_correct.

  (* delete *)
  forwards [(?&?) | (r1&h1&eq1)]: elim_if_success R; tryfalse.
  rewrite eq1 in R. simpl in R.
  case_if in R; inverts R.
   apply* red_delete_false.
   apply* red_delete_true.

  (* typeof *)
  forwards [(?&?) | (r1&h1&eq1)]: elim_if_success R; tryfalse.
  rewrite eq1 in R. simpl in R.
  forwards [(v1&eqr) | [(l&f&diffno&eqr&eqres) | (f&eqr&eqres)]]: elim_if_is_null_ref R.
    rewrite eqr in R. simpl in R.
     forwards [? | (v2&eqv2)]: elim_if_defined R.
       rewrite H in R. simpl in R. forwards*: wrong_not_ret R.
     rewrite eqv2 in R. simpl in R. inverts R.
     forwards~ R1: run_correct eq1.
     forwards* (OK'&OKL'&OKr1): sub_safety R1.
     apply* red_typeof_value.
       subst r1. constructor.
     apply* typeof_comp_correct.
    clear R. symmetry in eqres.
     forwards [? | (v2&eqv2)]: elim_if_defined eqres.
       rewrite H in eqres. simpl in eqres. forwards*: wrong_not_ret eqres.
     rewrite eqv2 in eqres. simpl in eqres.
     forwards [? | (v3&eqv3)]: elim_if_defined eqres.
       rewrite H in eqres. simpl in eqres. forwards*: wrong_not_ret eqres.
     rewrite eqv3 in eqres. simpl in eqres. inverts eqres.
     forwards~ R1: run_correct eq1.
     forwards* (OK'&OKL'&OKr1): sub_safety R1.
     apply* red_typeof_value.
       apply* getvalue_comp_correct.
     apply* typeof_comp_correct.
    clear R. inverts eqres.
     forwards~ R1: run_correct eq1. subst r1.
     apply* red_typeof_undefined.

  (* The four next cases are copy/pasted. *)
  (* pre_incr *)
  forwards [(?&?) | (r1&h1&eq1)]: elim_if_success R; tryfalse.
  rewrite eq1 in R. simpl in R.
  forwards [(eqw&v'&eqv') | (l&f&eq')]: elim_if_is_ref R.
    lets (h'0&eqw'): eqw. forwards*: wrong_not_ret eqw'.
  rewrite eq' in R. simpl in R.
  forwards [? | (v1&eqv1)]: elim_if_defined R.
    rewrite H in R. simpl in R. forwards*: wrong_not_ret R.
  destruct f; tryfalse.
  rewrite eqv1 in R. simpl in R.
  forwards [? | (v2&eqv2)]: elim_if_defined R.
    rewrite H in R. simpl in R. forwards*: wrong_not_ret R.
  rewrite eqv2 in R. simpl in R.
  inverts R. substs.
  forwards~ R1: run_correct eq1.
  forwards* (OK1&OKL1&OKr1): sub_safety R1.
  asserts OV1: (ok_value h1 v1).
    repeat case_if in eqv1; inverts eqv1. constructor*.
    lets OKV: ok_heap_ok_value OK1. unfolds in OKV.
    apply* OKV. rewrite* binds_equiv_read.
      apply* proto_indom. apply* proto_comp_correct.
        inverts~ OKr1. inverts* H0.
        apply* indom_bound.
      auto*.
  asserts OKV1': (ok_value h v1).
    inverts* OV1. false.
    rewrite~ binary_op_comp_fix in eqv2. simpl in eqv2.
    false eqv2.
    apply* red_pre_incr.
      apply* getvalue_comp_correct.
      apply* binary_op_comp_correct.
 
  (* post_incr *)
  forwards [(?&?) | (r1&h1&eq1)]: elim_if_success R; tryfalse.
  rewrite eq1 in R. simpl in R.
  forwards [(eqw&v'&eqv') | (l&f&eq')]: elim_if_is_ref R.
    lets (h'0&eqw'): eqw. forwards*: wrong_not_ret eqw'.
  rewrite eq' in R. simpl in R.
  forwards [? | (v1&eqv1)]: elim_if_defined R.
    rewrite H in R. simpl in R. forwards*: wrong_not_ret R.
  destruct f; tryfalse.
  rewrite eqv1 in R. simpl in R.
  forwards [? | (v2&eqv2)]: elim_if_defined R.
    rewrite H in R. simpl in R. forwards*: wrong_not_ret R.
  rewrite eqv2 in R. simpl in R.
  inverts R. substs.
  forwards~ R1: run_correct eq1.
  forwards* (OK1&OKL1&OKr1): sub_safety R1.
  asserts OV1: (ok_value h1 v1).
    repeat case_if in eqv1; inverts eqv1. constructor*.
    lets OKV: ok_heap_ok_value OK1. unfolds in OKV.
    apply* OKV. rewrite* binds_equiv_read.
      apply* proto_indom. apply* proto_comp_correct.
        inverts~ OKr1. inverts* H0.
        apply* indom_bound.
      auto*.
  asserts OKV1': (ok_value h v1).
    inverts* OV1. false.
    rewrite~ binary_op_comp_fix in eqv2. simpl in eqv2.
    false eqv2.
    apply* red_post_incr.
      apply* getvalue_comp_correct.
      apply* binary_op_comp_correct.

  (* pre_decr *)
  forwards [(?&?) | (r1&h1&eq1)]: elim_if_success R; tryfalse.
  rewrite eq1 in R. simpl in R.
  forwards [(eqw&v'&eqv') | (l&f&eq')]: elim_if_is_ref R.
    lets (h'0&eqw'): eqw. forwards*: wrong_not_ret eqw'.
  rewrite eq' in R. simpl in R.
  forwards [? | (v1&eqv1)]: elim_if_defined R.
    rewrite H in R. simpl in R. forwards*: wrong_not_ret R.
  destruct f; tryfalse.
  rewrite eqv1 in R. simpl in R.
  forwards [? | (v2&eqv2)]: elim_if_defined R.
    rewrite H in R. simpl in R. forwards*: wrong_not_ret R.
  rewrite eqv2 in R. simpl in R.
  inverts R. substs.
  forwards~ R1: run_correct eq1.
  forwards* (OK1&OKL1&OKr1): sub_safety R1.
  asserts OV1: (ok_value h1 v1).
    repeat case_if in eqv1; inverts eqv1. constructor*.
    lets OKV: ok_heap_ok_value OK1. unfolds in OKV.
    apply* OKV. rewrite* binds_equiv_read.
      apply* proto_indom. apply* proto_comp_correct.
        inverts~ OKr1. inverts* H0.
        apply* indom_bound.
      auto*.
  asserts OKV1': (ok_value h v1).
    inverts* OV1. false.
    rewrite~ binary_op_comp_fix in eqv2. simpl in eqv2.
    false eqv2.
    apply* red_pre_decr.
      apply* getvalue_comp_correct.
      apply* binary_op_comp_correct.

  (* post_decr *)
  forwards [(?&?) | (r1&h1&eq1)]: elim_if_success R; tryfalse.
  rewrite eq1 in R. simpl in R.
  forwards [(eqw&v'&eqv') | (l&f&eq')]: elim_if_is_ref R.
    lets (h'0&eqw'): eqw. forwards*: wrong_not_ret eqw'.
  rewrite eq' in R. simpl in R.
  forwards [? | (v1&eqv1)]: elim_if_defined R.
    rewrite H in R. simpl in R. forwards*: wrong_not_ret R.
  destruct f; tryfalse.
  rewrite eqv1 in R. simpl in R.
  forwards [? | (v2&eqv2)]: elim_if_defined R.
    rewrite H in R. simpl in R. forwards*: wrong_not_ret R.
  rewrite eqv2 in R. simpl in R.
  inverts R. substs.
  forwards~ R1: run_correct eq1.
  forwards* (OK1&OKL1&OKr1): sub_safety R1.
  asserts OV1: (ok_value h1 v1).
    repeat case_if in eqv1; inverts eqv1. constructor*.
    lets OKV: ok_heap_ok_value OK1. unfolds in OKV.
    apply* OKV. rewrite* binds_equiv_read.
      apply* proto_indom. apply* proto_comp_correct.
        inverts~ OKr1. inverts* H0.
        apply* indom_bound.
      auto*.
  asserts OKV1': (ok_value h v1).
    inverts* OV1. false.
    rewrite~ binary_op_comp_fix in eqv2. simpl in eqv2.
    false eqv2.
    apply* red_post_decr.
      apply* getvalue_comp_correct.
      apply* binary_op_comp_correct.

  (* void *) (* Note:  this is more or less a copy/paste of the proof of `not' above. *)
  forwards [(?&?) | [(v0&h1&eq1&eqv0) | (v0&h1&b'&eq1&eqv0)]]: elim_if_success_value R; tryfalse.
    rewrite eq1 in R. simpls. rewrite eqv0 in R. simpls. forwards*: wrong_not_ret R.
  rewrite eq1 in R. simpls. rewrite eqv0 in R. simpls.
  inverts~ R.
  forwards~ R': run_correct eq1.
  forwards* (OK1&OKL1&OKr1): sub_safety R'.
  apply* red_unary_op.
    apply* getvalue_comp_correct.
    apply* unary_op_comp_correct.

  (* binary_op *)
  forwards [(?&?) | [(v0&h1&eq1&eqv0) | (v0&h1&b'&eq1&eqv0)]]: elim_if_success_value R; tryfalse.
    rewrite eq1 in R. simpls. rewrite eqv0 in R. simpls. forwards*: wrong_not_ret R.
  rewrite eq1 in R. simpls. rewrite eqv0 in R. simpls.
  forwards [(?&?) | [(v1&h2&eq2&eqv1) | (v1&h2&b''&eq2&eqv1)]]: elim_if_success_value R; tryfalse.
    rewrite eq2 in R. simpls. rewrite eqv1 in R. simpls. forwards*: wrong_not_ret R.
  rewrite eq2 in R. simpls. rewrite eqv1 in R. simpls.
  forwards [? | (v3&eqv3)]: elim_if_defined R.
    rewrite H in R. simpl in R. forwards*: wrong_not_ret R.
  rewrite eqv3 in R. simpl in R.
  inverts* R.
  forwards* He1: run_correct eq1.
  forwards* (OK1&OKL1&OKr1): sub_safety He1.
  forwards* R2: run_correct eq2.
  forwards* (OK2&OKL2&OKr2&Ext'): safety R2.
  forwards* G0: getvalue_comp_correct eqv0.
  forwards* G1: getvalue_comp_correct eqv1.
  apply* red_binary_op.
  apply* binary_op_comp_correct.
    applys* ok_value_extends h1. forwards* O0: ok_result_prove G0.
     inverts~ O0.
    forwards* O1: ok_result_prove G1. inverts~ O1.

  (* and *)
  forwards [(?&?) | [(v0&h1&eq1&eqv0) | (v0&h1&b'&eq1&eqv0)]]: elim_if_success_value R; tryfalse.
    rewrite eq1 in R. simpls. rewrite eqv0 in R. simpls. forwards*: wrong_not_ret R.
  rewrite eq1 in R. simpls. rewrite eqv0 in R. simpls.
  forwards~ R1: run_correct eq1.
  forwards* (OK1&OKL1&OKr1): sub_safety R1.
  forwards [(?&?) | [(eq2&eqv) | (eq2&eqv)]]: elim_if_boolean R.
    forwards*: ret_not_wrong H.
    subst b'. simpls.
    forwards [(?&?) | [(v1&h2&eq3&eqv1) | (v1&h2&b''&eq3&eqv1)]]: elim_if_success_value R; tryfalse.
      rewrite eq3 in R. simpls. rewrite eqv1 in R. simpls. forwards*: wrong_not_ret R.
    rewrite eq3 in R; simpls. rewrite eqv1 in R. simpls.
     forwards~ R2: run_correct eq3.
     forwards* (OK2&OKL2&OKr2): sub_safety R2.
     inverts~ R.
     apply* red_and_true.
       apply* getvalue_comp_correct.
       apply* getvalue_comp_correct.
    inverts~ eq2.
     subst b'. simpls.
     apply* red_and_false.
       apply* getvalue_comp_correct.

  (* or *)
  forwards [(?&?) | [(v0&h1&eq1&eqv0) | (v0&h1&b'&eq1&eqv0)]]: elim_if_success_value R; tryfalse.
    rewrite eq1 in R. simpls. rewrite eqv0 in R. simpls. forwards*: wrong_not_ret R.
  rewrite eq1 in R. simpls. rewrite eqv0 in R. simpls.
  forwards~ R1: run_correct eq1.
  forwards* (OK1&OKL1&OKr1): sub_safety R1.
  forwards [(?&?) | [(eq2&eqv) | (eq2&eqv)]]: elim_if_boolean R.
    forwards*: ret_not_wrong H.
    subst b'. simpls.
     inverts~ R.
     apply* red_or_true.
       apply* getvalue_comp_correct.
    subst b'. simpls.
    forwards [(?&?) | [(v1&h2&eq3&eqv1) | (v1&h2&b''&eq3&eqv1)]]: elim_if_success_value R; tryfalse.
      rewrite eq3 in R. simpls. rewrite eqv1 in R. simpls. forwards*: wrong_not_ret R.
    rewrite eq3 in R. simpls. rewrite eqv1 in R. simpls.
     forwards~ R2: run_correct eq3.
     forwards* (OK2&OKL2&OKr2): sub_safety R2.
     inverts~ R.
     apply* red_or_false.
       apply* getvalue_comp_correct.
       apply* getvalue_comp_correct.

  (* assign *)
  destruct o.
  (* with an operator *)
  forwards [(?&?) | (r1&h1&eq1)]: elim_if_success R; tryfalse.
  rewrite eq1 in R. simpl in R.
  forwards [(eqw&v'&eqv') | (l&f&eq')]: elim_if_is_ref R.
    lets (h'0&eqw'): eqw. forwards*: wrong_not_ret eqw'.
  rewrite eq' in R. simpl in R.
  forwards [? | (v1&eqv1)]: elim_if_defined R.
    rewrite H in R. simpl in R. forwards*: wrong_not_ret R.
  rewrite eqv1 in R. simpl in R.
  forwards [(?&?) | [(r2&h2&eq2&eqv2) | (r2&h2&v2&eq2&eqv2)]]: elim_if_success_value R; tryfalse.
    rewrite eq2 in R. simpls. rewrite eqv2 in R. simpls. forwards*: wrong_not_ret R.
  rewrite eq2 in R. simpls. rewrite eqv2 in R. simpls.
  destruct f; tryfalse.
  subst r1.
  forwards [? | (v3&eqv3)]: elim_if_defined R.
    rewrite H in R. simpl in R. forwards*: wrong_not_ret R.
  rewrite eqv3 in R. simpl in R.
  inverts R.
  forwards* R1: run_correct eq1.
  forwards* (OK1&OKL1&OKr1&Ext1): safety R1.
  forwards* R2: run_correct eq2.
  forwards* (OK2&OKL2&OKr2&Ext2): safety R2.
  apply* red_assign_op.
    apply* getvalue_comp_correct.
    apply* getvalue_comp_correct.
    apply* binary_op_comp_correct.
      applys ok_value_extends Ext2.
      case_if in eqv1. case_if in eqv1.
       inverts* eqv1.
       inverts* eqv1. apply* ok_heap_ok_value.
       rewrite* binds_equiv_read.
       apply* proto_indom.
         apply* proto_comp_correct.
         apply* indom_bound.
         inverts OKr1.
         inverts* H0.
         auto*.
      inverts* OKr2.
       simpls. inverts~ eqv2.
       simpls. inverts~ eqv2.
       case_if in H1. case_if in H1.
        inverts* H1.
        inverts* H1. apply* ok_heap_ok_value.
        rewrite* binds_equiv_read.
        apply* proto_indom.
          apply* proto_comp_correct.
          apply* indom_bound.
          auto*.

  (* without *)
  forwards [(?&?) | (r1&h1&eq1)]: elim_if_success R; tryfalse.
  rewrite eq1 in R. simpl in R.
  forwards [(eqw&v'&eqv') | (l&f&eq')]: elim_if_is_ref R.
    lets (h'0&eqw'): eqw. forwards*: wrong_not_ret eqw'.
  rewrite eq' in R. simpl in R.
  forwards [(?&?) | [(v0&h2&eq2&eqv0) | (v0&h2&b&eq2&eqv0)]]: elim_if_success_value R; tryfalse.
    rewrite eq2 in R. simpls. rewrite eqv0 in R. simpls. forwards*: wrong_not_ret R.
  rewrite eq2 in R. simpls. rewrite eqv0 in R. simpls.
  inverts* R.
  forwards* R1: run_correct eq1.
  forwards* (OK1&OKL1&OKr1): sub_safety R1.
  inverts* OKr1; tryfalse.
  inverts H0.
  forwards* R2: run_correct eq2.
  forwards* (OK2&OKL2&OKr2): sub_safety R2.
  apply* red_assign.
  apply* getvalue_comp_correct.

  (* seq *)
  forwards [(?&?) | (r1&h1&eq1)]: elim_if_success R; tryfalse.
  rewrite eq1 in R. simpl in R.
  forwards [(?&?) | (r2&h2&eq2)]: elim_if_success R; tryfalse.
  rewrite eq2 in R. simpl in R.
  inverts* R.
  forwards~ R1: run_correct eq1.
  forwards* (OK1&OKL1&OKr1): sub_safety R1.
  forwards~ R2: run_correct eq2.
  forwards* (OK2&OKL2&OKr2): sub_safety R2.
  apply* red_seq.

destruct o. (* NEWSYNTAX -- reorganize the two cases *)
  (* var_decl_expr *)
  forwards [(?&?) | (v0&h0&eq)]: elim_if_success R; tryfalse.
  rewrite eq in R. simpl in R.
  forwards* R1: run_correct eq.
  inverts R.
  apply* red_var_decl_expr.
  (* var_decl *)
  inverts R.
  apply* red_var_decl.

destruct o. (* NEWSYTNAX --reorganized *) 
  (* if *)
  forwards [(?&?) | [(v0&h1&eq1&eqv0) | (v0&h1&b'&eq1&eqv0)]]: elim_if_success_value R; tryfalse.
    rewrite eq1 in R. simpls. rewrite eqv0 in R. simpls. forwards*: wrong_not_ret R.
  rewrite eq1 in R. simpls. rewrite eqv0 in R. simpls.
  forwards~ R1: run_correct eq1.
  forwards* (OK1&OKL1&OKr1): sub_safety R1.
  forwards [(?&?) | [(eq2&eqv) | (eq2&eqv)]]: elim_if_boolean R.
    forwards*: ret_not_wrong H.
    eapply red_if_true.
      apply* run_correct.
      subst b'. apply* getvalue_comp_correct.
      apply* run_correct.
  eapply red_if_false.
    apply* run_correct.
    subst b'. apply* getvalue_comp_correct.
    apply* run_correct.

  (* if *)
  forwards [(?&?) | [(v0&h1&eq1&eqv0) | (v0&h1&b'&eq1&eqv0)]]: elim_if_success_value R; tryfalse.
    rewrite eq1 in R. simpls. rewrite eqv0 in R. simpls. forwards*: wrong_not_ret R.
  rewrite eq1 in R. simpls. rewrite eqv0 in R. simpls.
  forwards~ R1: run_correct eq1.
  forwards* (OK1&OKL1&OKr1): sub_safety R1.
  forwards [(?&?) | [(eq2&eqv) | (eq2&eqv)]]: elim_if_boolean R.
    forwards*: ret_not_wrong H.
    eapply red_if_true.
      apply* run_correct.
      subst b'. apply* getvalue_comp_correct.
      apply* run_correct.
  inverts eq2.
  eapply red_if_false_implicit.
    apply* run_correct.
    subst b'. apply* getvalue_comp_correct.

  (* while *)
  forwards [(?&?) | [(v0&h1&eq1&eqv0) | (v0&h1&b'&eq1&eqv0)]]: elim_if_success_value R; tryfalse.
    rewrite eq1 in R. simpls. rewrite eqv0 in R. simpls. forwards*: wrong_not_ret R.
  rewrite eq1 in R. simpls. rewrite eqv0 in R. simpls.
  forwards~ R1: run_correct eq1.
  forwards* (OK1&OKL1&OKr1): sub_safety R1.
  forwards [(?&?) | [(_&eqv) | (_&eqv)]]: elim_if_boolean R.
    forwards*: ret_not_wrong H.
   subst b'. simpls.
    forwards [(?&?) | (r2&h2&eq2)]: elim_if_success R; tryfalse.
    rewrite eq2 in R. simpl in R.
    inverts R. apply* red_while_true. apply* getvalue_comp_correct.
   subst b'. simpls.
    inverts R. apply* red_while_false. apply* getvalue_comp_correct.

  (* with *)
  forwards [(?&?) | (r1&h1&eq1)]: elim_if_success R; tryfalse.
  rewrite eq1 in R. simpl in R.
  forwards [eqr | [(eqr&v'&eqo) | (l&eqo&diffno)]]: elim_if_not_eq R.
    rewrite eqr in R. simpl in R. forwards*: wrong_not_ret R.
    lets (h'0&eqr'): eqr. false (>> wrong_not_ret eqr').
  rewrite eqo in R. simpl in R.
  case_if in R. 
  forwards [(?&?) | (r2&h2&eq2)]: elim_if_success R; tryfalse.
  rewrite eq2 in R. simpl in R.
  inverts* R.
  forwards* R1: run_correct eq1.
  forwards* (OK1&OKL1&OKr1): sub_safety R1.
  forwards* R2: run_correct eq2.
    apply* ok_scope_cons.
    assert (ok_value h1 l).
      inverts OKr1; simpls.
      inverts* eqo.
      inverts H;
        case_if* in eqo; tryfalse.
      case_if* in eqo;
        tryfalse.
      inverts eqo.
      lets OKV1: ok_heap_ok_value OK1.
      unfold ok_heap_ok_value_def in OKV1.
      apply~ OKV1.
        rewrite* binds_equiv_read.
         apply* proto_indom.
         apply* proto_comp_correct.
         apply* indom_bound.
        split; discriminate.
    inverts* H.
  apply* red_with.
    apply* getvalue_comp_correct.

  (* skip *)
  inverts R.
  apply* red_skip.

  (* red_list_value *)
  intro m. destruct m.
    introv R OK OKL. false.
  introv R OK OKL. destruct es; simpl in R.
    do 2 eexists. splits*. constructor.
    forwards [(?&?) | [(v0&h2&eq2&eqv0) | (v0&h2&b&eq2&eqv0)]]: elim_if_success_value R; tryfalse.
      rewrite eq2 in R. simpls. rewrite eqv0 in R. simpls. forwards*: wrong_not_ret R.
    rewrite eq2 in R. simpls. rewrite eqv0 in R. simpls.
    rewrite <- (app_nil_l (b :: nil)) in R.
    forwards R': run_list_value_add_value R.
      introv. reflexivity.
    forwards~ Rc: run_correct eq2.
    forwards~ (O2&S2&Or2&E2): safety Rc.
    forwards~ (h4&vs'&E&Rl): run_list_value_correct R'.
    do 2 eexists. splits*.
    apply* red_list_cons.
    apply* getvalue_comp_correct.
Admitted. (* Admitted for the same reasons than the one of JsSafety:
             This proof requires a lot of memory and time! *)


(* Require a deterministic semantic:
Theorem run_complete : forall h h' L e v,
  red h L e h' v ->
  ok_heap h -> ok_scope h L ->
  exists m, run m h L e = out_return h' (ret_result v).
*)

End Correctness.

