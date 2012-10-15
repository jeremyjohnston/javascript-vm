Set Implicit Arguments.
Require Import JsSemanticsAux JsWf JsWfAux.
Implicit Types h : heap.

(**************************************************************)
(** ** Tactics *)

Hint Extern 1 (_ <> _ :> (loc*field)%type) => congruence.
Hint Extern 1 (_ <> _ :> field) => congruence.
Hint Extern 1 (field_normal_prototype <> _) => unfold field_normal_prototype.
Hint Extern 1 (_ <> field_normal_prototype) => unfold field_normal_prototype.


(**************************************************************)
(** ** Preservation of [has_some_proto] *)

Lemma has_some_proto_write : forall h l' l f v, 
  has_some_proto h l' ->
  has_some_proto (write h l f v) l'.
Proof. introv H. indom_simpl~. Qed.

Lemma has_some_proto_write_fields : forall h l' l fvs, 
  has_some_proto h l' ->
  has_some_proto (write_fields h l fvs) l'.
Proof. lets: has_some_proto_write. intros. apply* write_fields_ind. Qed.

Lemma has_some_proto_rem : forall h l' l f, 
  has_some_proto h l' ->
  f <> field_proto -> 
  has_some_proto (rem h l f) l'.
Proof. introv H N. apply* indom_rem. Qed.

Hint Resolve has_some_proto_write has_some_proto_rem.


(**************************************************************)
(** ** Preservation of [has_null_proto] *)

Lemma has_null_proto_write : forall h l' l f v, 
  has_null_proto h l' ->
  f <> field_proto ->
  has_null_proto (write h l f v) l'.
Proof. introv H N. apply* binds_write_neq. Qed.

Lemma has_null_proto_rem : forall h l' l f, 
  has_null_proto h l' ->
  f <> field_proto -> 
  has_null_proto (rem h l f) l'.
Proof. introv H N. apply* binds_rem. Qed.

Hint Resolve has_null_proto_write has_null_proto_rem.


(**************************************************************)
(** ** Preservation of [extends_proto] *)

Lemma extends_proto_write : forall h l f v, 
  extends_proto h (write h l f v).
Proof. introv H. auto~. Qed.

Lemma extends_proto_write_fields : forall h l fvs, 
  extends_proto h (write_fields h l fvs).
Proof. 
  hint extends_proto_write, extends_proto_trans.
  intros. apply* write_fields_ind.
Qed.

Lemma extends_proto_rem : forall h l f, 
  f <> field_proto ->
  extends_proto h (rem h l f).
Proof. introv N B. auto~. Qed.

Hint Resolve extends_proto_write extends_proto_write_fields.


(**************************************************************)
(** ** Preservation of [ok_scope] *)

Lemma ok_scope_write : forall h l s f v, 
  ok_scope h s -> 
  ok_scope (write h l f v) s. 
Proof. introv O. induction* O. Qed.

Lemma ok_scope_write_fields : forall h s l lfv,
  ok_scope h s ->
  ok_scope (write_fields h l lfv) s.
Proof.
introv O. apply~ write_fields_ind. introv O'.
apply* ok_scope_write.
Qed.

Lemma ok_scope_rem : forall h l f s, 
  ok_scope h s -> 
  f <> field_proto ->
  ok_scope (rem h l f) s. 
Proof. introv O N. induction* O. Qed.


(**************************************************************)
(** ** Preservation of [ok_value] *)

Lemma ok_value_write : forall h l f v v', 
  ok_value h v -> 
  ok_value (write h l f v') v. 
Proof.
  introv V. destruct V. 
  apply~ ok_value_basic.
  apply~ ok_value_loc.
Qed.

Lemma ok_value_rem: forall h l f v,
  ok_value h v ->
  f <> field_proto ->
  ok_value (rem h l f) v.
Proof.
  introv V NP. destruct V.
  apply* ok_value_basic.
  apply* ok_value_loc.
Qed.

Lemma ok_value_extends : forall h h' v,
  ok_value h v ->
  extends_proto h h' -> 
  ok_value h' v.
Proof. introv V E. inverts* V. Qed.


(**************************************************************)
(** ** Preservation of [protochain] *)

Lemma protochain_write_not_proto : forall h l l' f v, 
  protochain h l' ->
  f <> field_proto ->  
  protochain (write h l f v) l'.
Proof.
  introv C F. induction C.
  apply protochain_end.  
  applys protochain_step l'. binds_simpl~. auto.
Qed.

Lemma protochain_write_proto : forall h h' l l' v,
  protochain h l' ->
  h' = write h l field_proto v ->
  protochain h' l ->
  protochain h' l'.
Proof.
  introv C E L. subst. induction C.
  apply protochain_end.
  tests: (l0 = l).
    auto.
    apply* protochain_step. binds_simpl*. 
Qed. 

Lemma protochain_add_proto : forall h l l' v,  
  protochain h l ->
  fresh h l' -> 
  protochain (write h l' field_proto v) l.
Proof.
  introv C F. induction C.
  constructors.
  constructors.
    binds_simpl.
      left. apply* fresh_binds_neq. 
      eauto.
    eauto.
Qed.

Lemma protochain_new_proto : forall h l l',
  protochain h l ->
  fresh h l' ->
  protochain (write h l' field_proto l) l'.
Proof. introv P F. protochain_step. apply* protochain_add_proto. Qed.

Lemma protochain_rem : forall h l l' f,
  protochain h l ->
  f <> field_proto ->
  protochain (dealloc h (Ref l' f)) l.
Proof.
  introv C N. induction C.
  constructor.
  apply* protochain_step. apply* binds_rem.
Qed.


(**************************************************************)
(** ** Preservation of [ok_heap_special] *)

Lemma ok_heap_special_write : forall h l f v,
  ok_heap_special_def h -> 
  l <> loc_null -> 
  (l,f) <> (loc_scope,field_this) ->
  ok_heap_special_def (write h l f v).
Proof. 
  introv [H1 H2 H3 H4] N1 N2. constructors. 
  binds_simpl~. rewrite <- not_and. intros [E1 E2]. false.
  indom_simpl~.
  indom_simpl~.
  indom_simpl~.
Qed.

Lemma ok_heap_special_rem : forall h l x,
  ok_heap_special_def h -> 
  ok_heap_special_def (rem h l (field_normal x)).  
Proof.
  introv [H1 H2 H3 H4]. constructors.
  apply* binds_rem.
  apply* indom_rem.
  apply* indom_rem.
  apply* indom_rem.
Qed.


(**************************************************************)
(** ** Preservation of [ok_heap_protochain] *)

Section OkHeapProto.

Hint Resolve protochain_write_not_proto.

Lemma ok_heap_protochain_write_not_proto : forall h l f v,
  ok_heap_protochain_def h -> 
  let h' := write h l f v in
  f <> field_proto ->
  protochain h' l ->
  ok_heap_protochain_def h'.
Proof. introv M N B R. binds_cases* R. Qed.

Lemma ok_heap_protochain_write_proto : forall h l v,
  ok_heap_protochain_def h -> 
  let h' := write h l field_proto v in
  protochain h' l ->
  ok_heap_protochain_def h'.
Proof.
  introv B C R. binds_cases R.
  auto.
  apply* protochain_write_proto.
Qed.

Lemma ok_heap_protochain_rem : forall h l f,
  ok_heap_protochain_def h -> 
  f <> field_proto ->
  ok_heap_protochain_def (rem h l f).
Proof.
  introv W N B.
  forwards [_ ?]: binds_rem_inv B. apply* protochain_rem.
Qed.

End OkHeapProto.


(**************************************************************)
(** ** Preservation of [ok_heap_loc] *)

Lemma ok_heap_ok_value_write : forall h l f v,
  ok_heap_ok_value_def h -> 
  ok_value h v -> 
  ok_heap_ok_value_def (write h l f v).
Proof.
  introv O V B N. destruct V. 
    binds_cases* B. apply* ok_value_write.
    binds_cases* B. apply* ok_value_write.
Qed.

Lemma ok_heap_ok_value_write_scope_body : forall h l f v,
  ok_heap_ok_value_def h -> 
  f = field_scope \/ f = field_body ->
  ok_heap_ok_value_def (write h l f v).
Proof.
  introv O V B N. unfolds in N. destruct V. 
    binds_cases* B. apply* ok_value_write.
    binds_cases* B. apply* ok_value_write.
Qed.

Lemma ok_heap_ok_value_rem : forall h l x,
  ok_heap_ok_value_def h -> 
  ok_heap_ok_value_def (dealloc h (Ref l (field_normal x))).
Proof. 
  introv O B N. lets (B1&B2): binds_rem_inv B. 
  apply* ok_value_rem.
Qed.


(**************************************************************)
(** ** Preservation of [ok_heap_this] *)

Lemma ok_heap_this_write_not_this : forall h l f v,
  ok_heap_this_def h ->
  f <> field_this ->
  (f = field_proto -> indom h l field_this -> v = value_loc loc_null) ->
  ok_heap_this_def (write h l f v). 
Proof.
  introv O T P H. binds_cases H.
  lets (l'&F&N&HP): O H. exists l'. splits*.
  tests: (l0 = l /\ f = field_proto).
    inverts C. rewrite~ P. binds_simpl. apply* binds_indom.
    apply* binds_write_neq.
Qed.

Lemma ok_heap_this_write_this : forall h l l',
  ok_heap_this_def h -> 
  has_null_proto h l ->
  has_some_proto h l' ->
  ok_heap_this_def (write h l field_this (value_loc l')).
Proof. 
  introv O N P H. binds_cases H.
    exists* l'.
    lets (x&E&M&S): O H. exists* x.
Qed.

Lemma ok_heap_this_rem : forall h l x,
  ok_heap_this_def h -> 
  ok_heap_this_def (rem h l (field_normal x)).
Proof. 
  introv O B. lets (B1&B2): binds_rem_inv B.
  lets (y&E&N&S): O B2. exists* y.
Qed.


(**************************************************************)
(** ** Preservation of [ok_heap_function] *)

Lemma ok_heap_function_write_not_fun : forall h l f v,
  ok_heap_function_def h ->
  not_scope_or_body f ->
  ok_value h v ->
  ok_heap_function_def (write h l f v).
Proof. 
  introv O N NP B. unfolds in N. 
  forwards (s&x&e&l'&Bs&Bb&Bu): O.
    destruct B as [B|B]; binds_cases* B.
  exists s x e (If (Ref l f = Ref l0 field_normal_prototype) then v else l').
  splits.
    apply* binds_write_neq.
    apply* binds_write_neq.
    case_if as C. 
      inverts C. apply* binds_write_eq.
      apply* binds_write_neq. applys not_not_elim.
        intros M. rew_logic in M. false* C. inverts~ M. (* LATER: use tactic [down] *)
    apply* ok_scope_write.
Qed. 

Lemma ok_heap_function_alloc_fun : forall h l l' s x e,
  ok_heap_function_def h ->
  ok_scope h s ->
  has_some_proto h l ->
  ok_heap_function_def (alloc_fun h l' s x e l).
Proof.
  introv O S P B. destruct B.
  (* case: binds field_scope *)
  binds_cases* H.
    exists s x e l. splits*.
      apply* binds_write_neq. apply* binds_write_eq.
      apply* binds_write_eq. 
      do 2 apply* binds_write_neq. apply* binds_write_eq.
      do 4 apply* ok_scope_write. 
    forwards* (x'&e'&l1&B&E&F): O l0 v. exists x' e' l1 B.
     splits*; try (do 4 apply* binds_write_neq).
       do 4 apply* ok_scope_write.
  (* case: binds field_body (copy-pasted, but hard to factorize) *)
  binds_cases* H.
    exists s x e l. splits*.
      apply* binds_write_neq. apply* binds_write_eq.
      apply* binds_write_eq. 
      do 2 apply* binds_write_neq. apply* binds_write_eq.
       do 4 apply* ok_scope_write.
    forwards* (x'&e'&l1&B&E&F): O l0 v. exists x' e' l1 B.
     splits*; try (do 4 apply* binds_write_neq).
       do 4 apply* ok_scope_write.
Qed. 

Lemma ok_heap_function_rem : forall h l x,
  ok_heap_function_def h ->
  x <> "prototype"%string ->
  ok_heap_function_def (rem h l (field_normal x)).
Proof.
  introv O P B. destruct* B as [B|B];
    binds_cases* B; lets(N&B'): binds_rem_inv B.
  (* case: binds field_scope *)
  forwards* (s'&x'&e'&v'&Bs&Bb&Bu): O. exists s' x' e' v'.
   splits*; try (apply* binds_rem). apply* ok_scope_rem.
  (* case: binds field_body (copy-pasted, but hard to factorize) *)
  forwards* (s'&x'&e'&v'&Bs&Bb&Bu): O. exists s' x' e' v'.
   splits*; try (apply* binds_rem). apply* ok_scope_rem.
Qed.     


(**************************************************************)
(** ** Preservation of [ok_heap_null] *)

Lemma ok_heap_null_write : forall h l f v,
  ok_heap_null_def h ->
  l <> loc_null ->
  ok_heap_null_def (write h l f v).
Proof. introv O N. introv B. binds_cases* B. Qed.

Lemma ok_heap_null_rem : forall h l x,
  ok_heap_null_def h -> 
  ok_heap_null_def (rem h l (field_normal x)).
Proof. introv O B. lets* [? ?]: (binds_rem_inv B). Qed. 


(**************************************************************)
(** ** Lemmas about [ok_result] and [ok_value] *)

Lemma ok_result_loc : forall h l,
  has_some_proto h l -> 
  ok_result h l.
Proof. introv H. apply ok_result_value. apply~ ok_value_loc. Qed.

Lemma ok_result_prove : forall h v r,
  ok_heap h -> 
  ok_result h r -> 
  getvalue h r v -> 
  ok_result h v.
Proof. 
  introv O R G. inverts R as R.
  inverts~ G.
  inverts G as.
  (* case: getvalue_value *)
  introv G1 G2 G3 G4. apply ok_result_value. destruct~ v.
    (* subcase: v = loc *)
    intros. tests: (l = loc_null).
      apply* ok_value_basic.
      apply ok_value_loc. applys* ok_heap_binds_loc_has_proto O.
    (* subcase: v = value_scope j *)
    false (ok_heap_scope O G4).
    (* subcase: v = value_body j *)
    false (ok_heap_body O G4). 
  (* case: getvalue_undef *)
  intros. constructors. constructors. auto.
Qed.
 
Lemma ok_result_instanceof_red : forall h l v v',
  instanceof_red h l v v' -> 
  ok_result h v'.
Proof.
  introv H. induction* H.
Qed.

Lemma ok_result_binary_op_red : forall op v1 v2 v3 h,
  binary_op_red op h v1 v2 v3 -> 
  ok_result h v3.
Proof.
  introv H. induction* H.
  applys* ok_result_instanceof_red.
Qed.

Lemma ok_result_has_some_proto  : forall h l, 
  ok_result h (value_loc l) ->
  l <> loc_null -> 
  has_some_proto h l.
Proof. 
  introv O N. inverts O as O. inverts O as O.
  inverts O; tryfalse.
  auto.
Qed.

Hint Resolve ok_result_prove ok_result_binary_op_red ok_result_has_some_proto.

Lemma binds_this_loc_ok_result : forall h l l',
  binds h l field_this (value_loc l') ->
  ok_heap h ->
  ok_result h l'.
Proof.
  introv B O. apply ok_result_value. tests: (l' = loc_null).
    apply* ok_value_basic.
    apply ok_value_loc. forwards*: (ok_heap_ok_value O).
Qed.

Lemma obj_of_value_ok_result : forall h l l' v, 
  l = obj_of_value v l' ->
  ok_result h v ->
  has_some_proto h l' ->
  ok_result h l.
Proof.
  introv E V P.
  subst l. forwards [(l1&E)|?]: (value_loc_or_not v). 
    subst. simpl. case_if*.
    rewrite* obj_of_value_not_loc.
Qed.

Lemma getvalue_ok_value : forall h r v,
  getvalue h r v ->
  ok_result h r ->
  ok_heap h ->
  ok_value h v.
Proof.
  introv G R O. inverts R as R. 
  inverts~ G.
  destruct R.
    subst. inverts G; false.
    inverts G as M1 M2 M3 M4.
      destruct v; try solve [ apply~ ok_value_basic ].
        tests: (l = loc_null).
          apply~ ok_value_basic.
          apply ok_value_loc. forwards*: (ok_heap_ok_value O M4). 
        forwards*: (ok_heap_ok_value O M4). 
        forwards*: (ok_heap_ok_value O M4). 
      apply~ ok_value_basic.
Qed.


(**************************************************************)
(** ** Lemmas about [ok_scope] *)

Lemma ok_scope_inv_nil : forall h l s,
  ok_scope h (l :: s) -> s <> nil -> ok_scope h s.
Proof. introv O N. inverts O. false. auto. Qed. 

Lemma ok_scope_inv : forall h h' l s,
  ok_scope h (l :: s) -> ok_scope h' s -> ok_scope h s.
Proof. introv O O'. apply* ok_scope_inv_nil. inverts O'; congruence. Qed. 

Hint Resolve ok_scope_inv.


(**************************************************************)
(** ** Lemmas for hard cases of the proof of safety *)

Section Safety.
Hint Resolve ok_heap_special ok_heap_protochain.

(** Lemma for proving safety of [red_variable] *)

Lemma ok_result_variable_lookup : forall h s (l:loc) (x:string),
  scopes h x s l ->
  ok_heap h ->
  ok_scope h s ->
  ok_result h (result_ref (Ref l (field_normal x))).
Proof.
  introv H W O. inductions H.
  (* case: scope_null *)
  inverts O.
  (* case: scopes_here *)
  constructors. right. inverts H.
    false.
    inverts O.
      apply* protochain_has_some_proto. apply* ok_heap_protochain_def_indom.
      auto.
    forwards*: binds_indom H2.
  (* case: scopes_next *)
  asserts [M|M]: (l' = loc_null \/ s <> nil).
    inverts H0; congruence_on_disjunction.
    apply* ok_result_ref.
    apply* IHscopes. apply* ok_scope_inv_nil.
Qed.

(** Lemma for proving safety of [red_literal] *)

Lemma ok_result_value_of_literal : forall h i,
  ok_result h (value_of_literal i).
Proof.
  intros. applys ok_result_value.
  destruct i; simple~.
Qed.

(** Lemma for proving safety of [red_new] *)

Lemma obj_or_glob_of_value_protochain : forall h1 h2 l1 l2 f v1,
  binds h1 l1 f v1 ->
  l2 = obj_or_glob_of_value v1 ->
  extends_proto h1 h2 ->
  ok_heap h1 ->
  ok_heap h2 -> 
  not_scope_or_body f ->
  protochain h2 l2.
Proof. 
  introv B L E O1 O2 N. subst l2.
  forwards~: ok_heap_protochain_indom loc_obj_proto O2.
  forwards [(l3&E1)|?]: (value_loc_or_not v1).
    subst v1. simpl. case_if*.
     forwards* V: ok_heap_ok_value B. inverts V as M.
       inverts* M.
       applys~ ok_heap_protochain_indom. applys E M.
    rewrite~ obj_or_glob_of_value_not_loc.
Qed.  

Lemma ok_heap_alloc_obj : forall h l l', 
  protochain h l ->
  (l = loc_null \/ has_some_proto h l) ->
  fresh h l' ->
  ok_heap h ->
  ok_heap (alloc_obj h l' l).
Proof.
  unfold alloc_obj, write_proto.
  introv C P F [O1 O2 O3 O4 O5 O6]. constructors.
  apply* ok_heap_protochain_write_proto. apply* protochain_new_proto.
  destruct P.
    subst l. apply* ok_heap_ok_value_write. 
    apply* ok_heap_ok_value_write.
  apply* ok_heap_this_write_not_this.
   introv _ M. false* fresh_not_indom.
  apply* ok_heap_function_write_not_fun. destruct P.
    constructor. subst l.
    apply basic_null.  
  apply* ok_value_loc.
  apply* ok_heap_null_write.
  apply* ok_heap_special_write.
Qed.

Lemma ok_heap_alloc_fun : forall h l' s x e l, 
  ok_scope h s ->
  has_some_proto h l ->
  fresh h l' ->
  ok_heap h ->
  ok_heap (alloc_fun h l' s x e l).
Proof. 
  introv S P F [OP OL OT OF ON OS]. constructors. 
   lets FP: ok_heap_special_function_proto OS.
  hint protochain_write_not_proto.
   sets h': (write h l' field_proto loc_func_proto).
   asserts H': (protochain h' l').
     apply* protochain_new_proto.
      lets (v&B): indom_binds FP. forwards*: OP v.   
  do 3 apply* ok_heap_protochain_write_not_proto.
   apply* ok_heap_protochain_write_proto.
   lets FP: ok_heap_special_function_proto OS.
   do 2 apply* ok_heap_ok_value_write_scope_body.
   do 2 apply* ok_heap_ok_value_write.
  do 4 (apply ok_heap_this_write_not_this; auto_false).
   intros _ M. lets*: fresh_not_indom M.
  apply* ok_heap_function_alloc_fun. 
  do 4 apply* ok_heap_null_write.
  do 3 apply* ok_heap_special_write.
    apply* ok_heap_special_write.
    unfolds~ field_normal_prototype.
Qed.

Lemma ok_heap_write_user : forall h l x v, 
  ok_value h v ->
  has_some_proto h l -> 
  l <> loc_null ->
  ok_heap h ->
  ok_heap (write h l (field_normal x) v).
Proof.
  introv K R L O. lets [OP OL OT OF ON OS]: O.
  constructors.
  apply* ok_heap_protochain_write_not_proto.
   apply* protochain_write_not_proto.
   apply* ok_heap_protochain_def_indom.
  apply* ok_heap_ok_value_write.
  apply* ok_heap_this_write_not_this. auto_false.
  apply* ok_heap_function_write_not_fun.
  apply~ ok_heap_null_write.
  apply~ ok_heap_special_write.
Qed.

Lemma ok_heap_write_fields_user_undef : forall h l ys, 
  has_some_proto h l -> 
  l <> loc_null ->
  ok_heap h ->
  ok_heap (write_fields h l (map (fun y => (field_normal y, value_undef)) ys)).
Proof.
  introv R L O. 
  sets_eq fvs: (map (fun y => (field_normal y, value_undef)) ys).
  gen ys. apply write_fields_ind; clear fvs.
  introv E. auto.
  introv IH E. lets [?|(y&ys'&E')]: (case_last ys); 
   subst ys; rew_list in E.
    false* last_eq_nil_inv.
    lets [M1 M2]: last_eq_last_inv (rm E). inverts M2.
    hint has_some_proto_write_fields. apply* ok_heap_write_user.
Qed.

Lemma ok_heap_write_fields_user : forall h l fvs,
  has_some_proto h l -> 
  l <> loc_null ->
  ok_heap h ->
  Forall (fun c => let '(f, v) := c in
    ok_value h v /\ is_field_normal f) fvs ->
  ok_heap (write_fields h l fvs).
Proof.
  introv R L O.
  apply write_fields_ind.
  auto.
  introv Fu IH. forwards~ ((OV & y & ?) & Fu0): Forall_last_inv IH. subst.
   apply~ ok_heap_write_user.
     inverts~ OV. apply~ ok_value_loc. apply~ has_some_proto_write_fields.
     apply~ has_some_proto_write_fields.
Qed.

Lemma ok_heap_rem : forall h l x,
  ok_heap h ->
  x <> "prototype"%string -> 
  ok_heap (rem h l (field_normal x)).
Proof.
  introv [O1 O2 O3 O4 O5 O6] NP. constructors.
  apply* ok_heap_protochain_rem.
  apply* ok_heap_ok_value_rem.
  apply* ok_heap_this_rem.
  apply* ok_heap_function_rem. 
  apply* ok_heap_null_rem.
  apply* ok_heap_special_rem.
Qed.

Lemma ok_heap_write_this: forall h h' l l' v,
  ok_heap h ->
  has_null_proto h' l ->
  l <> loc_null ->
  l <> loc_scope ->
  h' = write h l field_this v ->
  v = value_loc l' ->
  has_some_proto h' l' ->
  ok_heap h'.
Proof.
  introv O N NN NS W V P. subst h'.
  lets [OP OL OT OF ON OS]: O. constructors*.
  apply* ok_heap_protochain_write_not_proto. 
   subst v. apply* protochain_step. constructor.
  apply* ok_heap_ok_value_write.
   subst v. apply* ok_value_loc. applys* indom_write_inv P. 
  subst v. apply* ok_heap_this_write_this.
    unfolds has_null_proto. binds_cases* N.
    unfolds has_some_proto. forwards*: indom_write_inv P.
  apply* ok_heap_function_write_not_fun.
  destruct v; try solve [constructors*|auto_false].
    rewrite V. apply ok_value_loc. applys* indom_write_inv P.
  apply~ ok_heap_null_write.
  apply* ok_heap_special_write. 
Qed.

Lemma arguments_ok_value : forall lx lv lfv h,
  arguments lx lv lfv ->
  Forall (ok_value h) lv ->
  Forall (fun c => let '(f, v) := c in
    ok_value h v /\ is_field_normal f) lfv.
Proof.
  introv I. induction I; introv F; constructors.
  splits. inverts~ F. exists~ x.
  auto.
  splits. inverts~ F. unfolds*.
  inverts* F.
Qed.


(**************************************************************)
(** ** Tactics for the proof of safety *)

(** Automatisation of [ok_result] *)

Hint Extern 1 (ok_result ?h ?r) =>
  match goal with H: context [ok_result h ?r'] |- _ =>
    let M := fresh in 
    assert (M : ok_result h r'); [ | apply M ]
  end.

(** Automatisation of [extends_proto] *)

Lemma extends_proto_eq_trans : forall h1 h2 h3 h4, 
  h3 = h4 ->
  extends_proto h2 h4 ->
  extends_proto h1 h2 ->
  extends_proto h1 h3.
Proof.
  introv E E1 E2. subst. applys extends_proto_trans E2 E1.
Qed.

Lemma extends_proto_write_trans : forall h1 h2 l f v, 
  extends_proto h1 h2 ->
  extends_proto h1 (write h2 l f v).
Proof.
  introv H. applys extends_proto_trans H. 
  applys extends_proto_write.
Qed.

Lemma extends_proto_write_fields_trans : forall h1 h2 l fvs, 
  extends_proto h1 h2 ->
  extends_proto h1 (write_fields h2 l fvs).
Proof.
  introv H. applys extends_proto_trans H. 
  applys extends_proto_write_fields.
Qed.

Ltac extends_proto_step :=
  check_noevar_goal;
  first
  [ apply extends_proto_refl
  | apply extends_proto_write_fields_trans
  | apply extends_proto_write_trans
  | applys extends_proto_eq_trans; 
    [ eassumption
    | solve [ apply extends_proto_write_fields
            | apply extends_proto_write ] 
    | idtac ]
  | match goal with
    | H: context [ extends_proto ?h' ?h] |- extends_proto ?h' ?h => 
        solve [ forwards_nounfold ?: H; 
          match goal with 
          | |- extends_proto _ _ => solve [ jauto_set; assumption | fail 2 ]
          | |- _ => auto*
          end 
       | fail 2 ] 
    | H: context [ extends_proto ?h' ?h] |- extends_proto ?h'' ?h =>
       (match h'' with h' => fail 2 | _ => idtac end);
       eapply (@extends_proto_trans h'); 
        [ idtac
        | solve [ forwards_nounfold ?: H; clear H; auto* | fail 2 ] ]
    end
   ].

Ltac extends_proto_simpl :=
  repeat extends_proto_step. 

Hint Extern 1 (extends_proto _ _) => extends_proto_simpl.



(**************************************************************)
(** ** Proof of safety *)

Theorem safety : forall h s e h' r,
  red h s e h' r ->
  ok_heap h -> 
  ok_scope h s -> 
  ok_heap h' /\ 
  ok_scope h' s /\
  ok_result h' r /\
  extends_proto h h'
with safety_list : forall h s le h' lv,
    red_list_value h s le h' lv ->
    ok_heap h ->
    ok_scope h s ->
    ok_heap h' /\
    ok_scope h' s /\
    Forall (ok_value h') lv /\
    extends_proto h h'.
Proof.
  introv R. induction R; introv O S.

  (* red_this *) 
  hint binds_this_loc_ok_result. auto*.

  (* red_variable *)
  hint ok_result_variable_lookup. auto*.

  (* red_literal *)
  hint ok_result_value_of_literal. auto*.

  (* red_object *)
    lets[o1 o2 o3 o4 o5 [o6 o7 o8 o9]]: O.
    forwards* (a&b&c&d): safety_list.    
      subst h1. apply ok_heap_alloc_obj.
        lets*[v B]: indom_binds o8.
        right*. assumption. assumption.
      subst h1. apply* ok_scope_write.
    splits*.
      subst h3. apply* ok_heap_write_fields_user.
        apply* d. subst h1. indom_simpl.
        apply* arguments_ok_value.
      subst h3. apply* ok_scope_write_fields.
      subst h3. apply* ok_result_loc.
        apply* has_some_proto_write_fields.
        apply* d. subst h1. indom_simpl.

  (* red_function_unnamed *) 
  splits.
    hint ok_heap_protochain, ok_heap_special_obj_proto.
    rewrite H2. apply* ok_heap_alloc_fun.
      subst h1. apply* ok_scope_write.
      subst h1. indom_simpl_step.
      rewrite H0. apply* ok_heap_alloc_obj.
        apply* ok_heap_protochain_def_indom. 
        right. apply* ok_heap_special_obj_proto.  
    subst h1 h2. do 5 apply ok_scope_write. auto.
    subst h2. apply ok_result_loc. indom_simpl.
    auto.

  (* red_function_named *)
  asserts: (ok_scope h2 s).
    subst h1 h2. do 2 apply* ok_scope_write.
  splits.
    hint ok_heap_special_obj_proto.
     asserts O1: (ok_heap h1).
       subst h1. apply* ok_heap_alloc_obj.
         apply* ok_heap_protochain_def_indom. 
         right. apply* ok_heap_special_obj_proto.
     asserts O2: (ok_heap h2).
       subst h2. apply* ok_heap_alloc_obj.
         apply* ok_heap_protochain_def_indom. 
         right. apply* ok_heap_special_obj_proto.
     asserts O3: (ok_heap h3).
       subst h3. apply* ok_heap_alloc_fun. 
         constructors*. subst h2. indom_simpl.
         subst h2 h1. indom_simpl.
     subst h4. applys* ok_heap_write_user.
       apply ok_value_loc. subst h3. indom_simpl.
       subst h3 h2. indom_simpl.
    subst. repeat apply ok_scope_write. auto.
    subst h4 h3. apply ok_result_loc. indom_simpl.
    auto.

  (* red_eval *) 
  auto*.
  
  (* red_access *) 
  intuition eauto 7.

  (* red_member *)
   auto*.

  (* red_new *)  
  forwards (Oh1&Sh1&Rh1&Ph1): (rm IHR1) O S.
  forwards~ (O2&S2&OV2&E2): safety_list (rm H6).
  asserts O3: (ok_heap h3). subst h3. apply* ok_heap_alloc_obj. 
    applys* obj_or_glob_of_value_protochain h1 l1 field_normal_prototype v1.
    (* TODO: maybe factorize the prove of [has_some_proto h2 l2] with
       the fact that we have just established [proto_chain h2 l2] *)
    right. forwards~: ok_heap_special_obj_proto h1.
     subst l2. forwards [(l11&E11)|?]: (value_loc_or_not v1). 
       subst v1. simpl. forwards* OV: ok_heap_ok_value H4.
        case_if*. rewrite~ obj_or_glob_of_value_not_loc.
  asserts S3: (ok_scope h3 s). subst h3. apply* ok_scope_write.
  asserts O4: (ok_heap h4). subst h4. apply* ok_heap_alloc_obj. constructor.
  asserts S4: (ok_scope h4 s). subst h4. apply* ok_scope_write.
  asserts O5: (ok_heap h5). subst h5. forwards*: ok_heap_write_this h4 l3 l4 l4.
    subst h4. apply* binds_write_neq. apply* binds_write_eq.
    applys neq_sym. applys~ fresh_binds_neq h3.
     applys~ ok_heap_special_global_this.
    subst h4 h3. do 2 apply* indom_write. apply* indom_write_eq.
  asserts S5: (ok_scope h5 s). subst h5. apply* ok_scope_write.
  asserts O6: (ok_heap h6). subst h6. apply* ok_heap_write_fields_user.
    subst h5 h4 h3. apply* indom_write. indom_simpl.
    apply* arguments_ok_value.
     applys~ Forall_trans value (ok_value h2).
     introv Oa. applys~ ok_value_extends h2.
  asserts S6: (ok_scope h6 s). subst h6. apply* ok_scope_write_fields.
  asserts O7: (ok_heap h7). subst h7. apply* ok_heap_write_fields_user_undef.
    subst h6 h5 h4. apply* indom_write_fields. apply* indom_write. apply* indom_write_eq.
  asserts S7: (ok_scope h7 s). applys* ok_scope_extends. 
  forwards OS3: ok_heap_binds_ok_scope H1. auto*.
  asserts S7': (ok_scope h7 (l3 :: s3)). constructors.
    applys ok_scope_extends. eauto. extends_proto_simpl.
    subst h7 h6 h5 h4. apply* has_some_proto_write_fields. 
     apply* indom_write_fields. apply* has_some_proto_write. apply* indom_write_eq.
  asserts P4: (has_some_proto h3 l4). subst h3. apply* indom_write_eq.
  splits*.
    apply* ok_scope_extends.
    asserts~: (extends_proto h3 h8). 
     applys* obj_of_value_ok_result l4 v3.

  (* red_call *)
  forwards (?&M1&?&?): (rm IHR1). auto*. auto*.
  forwards~ (O2&S2&OV2&E2): safety_list (rm H5).
  forwards (?&M2&?&?): (rm IHR2).
    asserts: (has_some_proto h3 l3). subst h3. indom_simpl.
     subst h6. apply* ok_heap_write_fields_user_undef.
       subst h5 h4 h3. apply~ indom_write_fields. indom_simpl.
     subst h5. apply* ok_heap_write_fields_user.
       subst h4 h3. indom_simpl.
     subst h4. applys ok_heap_write_this h3 (@eq_refl).
     subst h3. apply* ok_heap_alloc_obj. constructor.
     subst h3. apply* binds_write_neq. apply* binds_write_eq.
     apply* fresh_not_null.
     applys neq_sym. applys~ fresh_binds_neq h2. 
      applys~ ok_heap_special_global_this.
     auto.
     destruct r1 as [v1|[l f]].
       subst l2 h3. do 2 apply* indom_write. 
        apply* ok_heap_special_global_proto.
       subst l2. unfold get_this. case_if.
         subst h3. do 2 apply* indom_write. 
          apply* ok_heap_special_global_proto.
         subst h3.
          do 2 apply* has_some_proto_write. inverts H as P N N' B.
           forwards~: proto_has_some_proto P.
     apply* arguments_ok_value.
     applys~ Forall_trans value (ok_value h2). (* LATER: remove `value' in Coq v8.4. *)
       introv Oa. applys~ ok_value_extends h2.
    asserts O3: (ok_heap h3).
      subst h3. apply* ok_heap_alloc_obj. constructors.       
     constructors.
       applys ok_scope_extends h1. 
         applys* ok_heap_binds_ok_scope H2.
         auto.
      subst h5 h6 h4 h3. apply indom_write_fields.
        apply indom_write_fields. indom_simpl.
  asserts: (extends_proto h2 h7). auto. (* useful to makes proof term smaller *)
  splits*. applys* ok_scope_extends.

  (* red_unary_op *)
  inverts* H0.

  (* red_typeof_value *)
  auto*.

  (* red_typeof_undefined *)
  auto*.

  (* The next four cases have the same proof. *)
  (* red_pre_incr *)
  forwards* (?&?&M&?): (rm IHR). subst h2.
  unfold update. sets l': (ifb l = loc_null then loc_global else l).
  splits.
    applys* ok_heap_write_user.
      inverts* H0.
      subst l'. case_if*.
        subst. applys* ok_heap_special_global_proto.
        applys* extends_proto_elim h1. inverts M as [?|?]; auto_false. 
      subst l'. case_if*; congruence.
    apply* ok_scope_write.
    apply ok_result_value. apply ok_value_write.
      inverts* H0.
    extends_proto_simpl.

  (* red_pre_decr *)
  forwards* (?&?&M&?): (rm IHR). subst h2.
  unfold update. sets l': (ifb l = loc_null then loc_global else l).
  splits.
    applys* ok_heap_write_user.
      inverts* H0.
      subst l'. case_if*.
        subst. applys* ok_heap_special_global_proto.
        applys* extends_proto_elim h1. inverts M as [?|?]; auto_false. 
      subst l'. case_if*; congruence.
    apply* ok_scope_write.
    apply ok_result_value. apply ok_value_write.
      inverts* H0.
    extends_proto_simpl.

  (* red_post_incr *)
  forwards* (?&?&M&?): (rm IHR). subst h2.
  unfold update. sets l': (ifb l = loc_null then loc_global else l).
  splits.
    applys* ok_heap_write_user.
      inverts* H0.
      subst l'. case_if*.
        subst. applys* ok_heap_special_global_proto.
        applys* extends_proto_elim h1. inverts M as [?|?]; auto_false. 
      subst l'. case_if*; congruence.
    apply* ok_scope_write.
    apply ok_result_value. apply ok_value_write.
      inverts* H0.
    extends_proto_simpl.

  (* red_post_decr *)
  forwards* (?&?&M&?): (rm IHR). subst h2.
  unfold update. sets l': (ifb l = loc_null then loc_global else l).
  splits.
    applys* ok_heap_write_user.
      inverts* H0.
      subst l'. case_if*.
        subst. applys* ok_heap_special_global_proto.
        applys* extends_proto_elim h1. inverts M as [?|?]; auto_false. 
      subst l'. case_if*; congruence.
    apply* ok_scope_write.
    apply ok_result_value. apply ok_value_write.
      inverts* H0.
    extends_proto_simpl.

  (* red_delete_true *)    
  forwards* (?&?&M&?): (rm IHR).
  unfolds dealloc. destruct r as [|[l f]].
    subst h2. splits~.
    subst h2. inverts M. splits.
       apply* ok_heap_rem.
       intro_subst; simpls; apply* H.
       apply* ok_scope_rem.
       apply~ ok_result_value.
       applys~ extends_proto_trans h1. applys~ extends_proto_rem.
 
  (* red_delete_false *) 
  auto*.

  (* red_binary_op *)
  auto*.

  (* red_and_true *)
  auto*.

  (* red_and_false *)
  auto*.

  (* red_or_true *)
  auto*.

  (* red_or_false *)
  auto*.

  (* red_in_true *)
  auto*.

  (* red_in_false *)
  auto*.

  (* red_assign *) 
  forwards* (?&?&M&?): (rm IHR1). forwards*: (rm IHR2). subst h3.
  unfold update. sets l': (ifb l = loc_null then loc_global else l).
  splits.
    applys* ok_heap_write_user. 
      apply* getvalue_ok_value.
      subst l'. case_if.
        subst. applys* ok_heap_special_global_proto.
        applys* extends_proto_elim h1. inverts M as [?|?]; auto_false. 
      subst l'. case_if; congruence.
    apply* ok_scope_write.
    apply ok_result_value. apply ok_value_write. apply* getvalue_ok_value.
    extends_proto_simpl.

  (* expr_assign_op *)
  forwards* (?&?&M&?): (rm IHR1). forwards*: (rm IHR2). subst h3.
  unfold update. sets l': (ifb l = loc_null then loc_global else l).
  lets Ov: ok_result_binary_op_red H1. hint getvalue_value.
  splits.
    applys* ok_heap_write_user. 
      apply* getvalue_ok_value.  
      subst l'. case_if.
        subst. applys* ok_heap_special_global_proto.
        applys* extends_proto_elim h1. inverts M as [?|?]; auto_false. 
      subst l'. case_if; congruence.
    apply* ok_scope_write.
    apply ok_result_value. apply ok_value_write. apply* getvalue_ok_value.
    extends_proto_simpl.

  (* red_seq *) 
  auto*.

  (* red_var_decl *)
  auto*.

  (* red_var_decl_expr *)
  auto*.

  (* red_if_true *) 
  auto*.

  (* red_if_false *) 
  auto*.

  (* red_if_false_implicit *) 
  auto*.

  (* red_while_true *) 
  auto*.

  (* red_while_false *) 
  auto*.

  (* red_with *) 
  forwards*: (rm IHR1). forwards* (?&M2&?&?): (rm IHR2).

  (* red_skip *)
  auto*.
 
  (* red_list_value *)
  Hint Constructors Forall.
  introv R. induction R; introv O S.

  (* nil *)
  auto.

  (* cons *)
  forwards~ (O2&S2&F2&E2): safety (rm H).
  forwards~ (O3&S3&F3&E3): (rm IHR).
  asserts: (ok_value h3 v).
    applys~ ok_value_extends h2. applys~ getvalue_ok_value H0.
  auto.

(* Arthur replaced Qed by Admitted to save your machine
   for spending 5 minutes filling 1.5 Gb of RAM just to
   inspect the full proof term for this proof. *)
Admitted.

End Safety.

