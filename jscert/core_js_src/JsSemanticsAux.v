Set Implicit Arguments.
Require Import LibLogic LibHeap.
Require Export JsSemantics. 
Implicit Type h : heap.
Implicit Type l : loc.
Implicit Type f : field.


(**************************************************************)
(**************************************************************)
(** * Auxiliary lemmas *)


(**************************************************************)
(** * Checking the type of fields *)

(** Express whether a field is a user field *)

Definition is_field_normal f :=
    exists y, f = field_normal y.


(**************************************************************)
(** * Comparison of references *)

Lemma ref_neq : forall l l' f f',
  (Ref l f <> Ref l' f') = (l <> l' \/ f <> f').
Proof.
  intros. extens. iff H.
  rewrite <- not_and. intros [? ?]. subst. apply~ H.
  intros M. inverts M. destruct H; congruence.
Qed.

Lemma ref_neq_inv : forall l l' f f',
  (Ref l f <> Ref l' f') -> (l <> l' \/ f <> f').
Proof. intros. rewrite~ <- ref_neq. Qed.

Lemma ref_neq_prove : forall l l' f f',
  (l <> l' \/ f <> f') -> (Ref l f <> Ref l' f').
Proof. intros. rewrite~ ref_neq. Qed.


(**************************************************)
(** * Induction principle for [red] *)

Section Red_induct.

Scheme red_ind' := Induction for red Sort Prop
  with red_list_value_ind' := Induction for red_list_value Sort Prop.

Combined Scheme red_list_ind from red_ind', red_list_value_ind'.
 
End Red_induct.


(**************************************************************)
(** ** Corrolaries for [obj_of_value] *)

Definition value_not_loc v := 
  forall l, v <> value_loc l.

Lemma value_loc_or_not : forall v,
  (exists l, v = value_loc l) \/ (value_not_loc v).
Proof.
  intros. applys classic_right. introv M.
  rew_logic in M. auto.
Qed.

Lemma obj_of_value_not_loc : forall v l',
  value_not_loc v -> 
  obj_of_value v l' = l'.
Proof. introv H. destruct* v. false* H. Qed.


(**************************************************************)
(** ** Corrolaries for [obj_or_glob_of_value_not_loc] *)

Definition not_scope_or_body f := 
  f <> field_scope /\ f <> field_body.

Hint Unfold not_scope_or_body.

Lemma obj_or_glob_of_value_not_loc : forall v,
  value_not_loc v -> 
  obj_or_glob_of_value v = loc_obj_proto.
Proof. introv H. destruct* v. simpl. false* H. Qed.



(**************************************************************)
(**************************************************************)
(** * Properties of heaps *)

(**************************************************************)
(** * Properties of heaps (adapted from module [Heap]) *)

Section Properties.
Hint Resolve ref_neq_inv ref_neq_prove.

(** DO NOT REORDER THE LEMMAS *)

Lemma binds_equiv_read : forall h l f,
  indom h l f -> (forall v, (binds h l f v) = (read h l f = v)).
Proof. intros. apply* @Heap.binds_equiv_read. Qed.

Lemma indom_equiv_binds : forall h l f,
  indom h l f = (exists v, binds h l f v).
Proof. intros. apply Heap.indom_equiv_binds. Qed.

Lemma binds_write_eq : forall h l f v,
  binds (write h l f v) l f v.
Proof. intros. apply Heap.binds_write_eq. Qed.

Lemma binds_write_neq : forall h l f v l' f' v',
  binds h l f v -> (l <> l' \/ f <> f') -> 
  binds (write h l' f' v') l f v.
Proof.
  introv B N. applys @Heap.binds_write_neq B.
  destruct N; congruence.
Qed.

Lemma binds_write_inv : forall h l f v l' f' v',
  binds (write h l' f' v') l f v -> 
     (l = l' /\ f = f' /\ v = v') 
  \/ ((l <> l' \/ f <> f') /\ binds h l f v). 
Proof.
  introv B. forwards [[E ?]|[E ?]]: @Heap.binds_write_inv B.
  inverts E. left*.
  right*.
Qed.

Lemma binds_rem : forall h l f l' f' v,
  binds h l f v -> (l <> l' \/ f <> f') -> binds (rem h l' f') l f v.
Proof. introv B N. apply* @Heap.binds_rem. Qed.

Lemma binds_rem_inv : forall h l f v l' f',
  binds (rem h l' f') l f v -> (l <> l' \/ f <> f') /\ binds h l f v.
Proof. introv B. forwards* [? ?]: @Heap.binds_rem_inv B. Qed.

Lemma not_indom_rem : forall h l f,
  ~ indom (rem h l f) l f.
Proof. intros. apply Heap.not_indom_rem. Qed.

Lemma indom_binds : forall h l f, 
  indom h l f -> exists v, binds h l f v.
Proof. intros. apply* @LibHeap.indom_binds. Qed.

Lemma binds_indom : forall h l f v, 
  binds h l f v -> indom h l f.
Proof. intros. apply* @LibHeap.binds_indom. Qed.

Lemma binds_func : forall h l f v v',
  binds h l f v -> binds h l f v' -> v = v'.
Proof. intros. applys* @LibHeap.binds_func; typeclass. Qed.

Lemma binds_read : forall h l f v,
  binds h l f v -> read h l f = v.
Proof. intros. apply* @LibHeap.binds_read. Qed.

Lemma read_binds : forall h l f v,
  read h l f = v -> indom h l f -> binds h l f v.
Proof. intros. apply* @LibHeap.read_binds. Qed.

Lemma read_write_eq : forall h l f v, 
  read (write h l f v) l f = v.
Proof. intros. apply* @LibHeap.read_write_eq. Qed.

Lemma read_write_neq : forall h l f l' f' v', 
  indom h l f -> (l <> l' \/ f <> f') -> read (write h l' f' v') l f = read h l f.
Proof. intros. apply* @LibHeap.read_write_neq. Qed.

Lemma indom_write_eq : forall h l f v,
  indom (write h l f v) l f.
Proof. intros. apply* @LibHeap.indom_write_eq. Qed.

Lemma indom_write : forall h l f l' f' v',
  indom h l f -> indom (write h l' f' v') l f.
Proof. intros. apply* @LibHeap.indom_write. Qed.

Lemma indom_write_inv : forall h l f l' f' v',
  indom (write h l' f' v') l f -> (l <> l' \/ f <> f') -> indom h l f.
Proof. intros. apply* @LibHeap.indom_write_inv. Qed.  

Lemma binds_write_eq_inv : forall h l f v v',
  binds (write h l f v') l f v -> v = v'.
Proof. intros. apply* @LibHeap.binds_write_eq_inv. Qed.

Lemma binds_write_neq_inv : forall h l f v l' f' v',
  binds (write h l' f' v') l f v -> (l <> l' \/ f <> f') -> binds h l f v. 
Proof. intros. apply* @LibHeap.binds_write_neq_inv. Qed.  

Lemma indom_rem : forall h l f l' f',
  indom h l f -> (l <> l' \/ f <> f') -> indom (rem h l' f') l f.
Proof. intros. apply* @LibHeap.indom_rem. Qed.

Lemma indom_rem_inv : forall h l f l' f',
  indom (rem h l f) l' f' -> (l <> l' \/ f <> f') /\ indom h l' f'.
Proof. intros. forwards* [? ?]: @LibHeap.indom_rem_inv H. Qed.

Lemma read_rem_neq : forall h l f l' f',
  indom h l f -> (l <> l' \/ f <> f') -> read (rem h l' f') l f = read h l f.
Proof. intros. apply* @LibHeap.read_rem_neq. Qed.

Lemma not_indom_empty : forall l f,
  ~ indom empty_heap l f.
Proof. intros. apply* @LibHeap.not_indom_empty. Qed.

Lemma not_binds_empty : forall l f v,
  ~ binds empty_heap l f v.
Proof. intros. apply* @LibHeap.not_binds_empty. Qed.

End Properties.


(**************************************************************)
(** * Other results *)

(** [binds] on location is functional *)

Lemma binds_func_loc : forall h f l l1 l2,
  binds h l f (value_loc l1) ->
  binds h l f (value_loc l2) ->
  l1 = l2.
Proof. introv B1 B2. forwards E: binds_func B1 B2. inverts~ E. Qed.

(** Checking if a location l is bound to a given value in the heap
    is decidable. *)

Global Instance indom_decidable : forall h l f,
  Decidable (indom h l f).
Proof. intros. apply Heap.indom_decidable. Qed.



(**************************************************************)
(** * Properties of write_fields *)

Lemma write_fields_nil : forall h l,
  write_fields h l nil = h.
Proof. auto. Qed.

Lemma write_fields_cons : forall h l f v fvs,
  write_fields h l ((f,v)::fvs) = write_fields (write h l f v) l fvs.
Proof. auto. Qed.

Hint Rewrite write_fields_nil write_fields_cons : rew_write_fields.
Ltac rew_write_fields := autorewrite with rew_write_fields.

(** An induction principle for proving facts about [write_fields] *)

Lemma write_fields_ind : forall (P : list(field*value)->heap->heap->Prop), forall l h,
  (P nil h h) ->
  (forall f v fvs, P fvs h (write_fields h l fvs) -> P (fvs&(f,v)) h (write (write_fields h l fvs) l f v)) ->
  (forall fvs, P fvs h (write_fields h l fvs)).
Proof.
  introv MN MC. intros. unfold write_fields. induction fvs using list_ind_last; rew_list.
  auto. destruct a as [f' v']. apply~ MC.
Qed.

Lemma binds_write_fields_neq : forall h l f v l' fvs',
  binds h l f v -> l <> l' -> 
  binds (write_fields h l' fvs') l f v.
Proof. intros. lets: binds_write_neq. apply* write_fields_ind. Qed.

Lemma binds_write_fields_neq_inv : forall h l l' fvs' f v,
  binds (write_fields h l' fvs') l f v -> l <> l' -> binds h l f v. 
Proof. introv B N. gen B. lets: binds_write_neq_inv. apply* write_fields_ind. Qed.

Lemma indom_write_fields : forall h l f l' fvs',
  indom h l f -> indom (write_fields h l' fvs') l f.
Proof. introv D. lets: indom_write. apply* write_fields_ind. Qed.


(**************************************************************)
(** * Properties of bound *)

Lemma binds_bound : forall h l f v,
  binds h l f v -> bound h l.
Proof. intros. exists f. apply* binds_indom. Qed.

Lemma indom_bound : forall h l f,
  indom h l f -> bound h l.
Proof. intros. exists* f. Qed.

Lemma not_bound_indom : forall h l f, 
  (~ bound h l) -> indom h l f -> False.
Proof. introv N D. apply N. apply* indom_bound. Qed.

Lemma not_bound_binds : forall h l f v,
  (~ bound h l) -> binds h l f v -> False.
Proof. introv N D. apply N. apply* binds_bound. Qed.

Lemma bound_binds : forall h l,
  bound h l -> exists f v, binds h l f v.
Proof. introv [f D]. rewrite* indom_equiv_binds in D. Qed.


(**************************************************************)
(** * Properties of freshness *)

Lemma fresh_not_null : forall h l,
  fresh h l -> l <> loc_null.
Proof. introv [N _]. auto. Qed.

Hint Resolve fresh_not_null.

(** Elimination of fresh *)

Lemma fresh_not_bound : forall h l,
  fresh h l -> bound h l -> False.
Proof. introv [_ N] D. false. Qed.

Lemma fresh_bound_neq : forall h l l', 
  fresh h l' -> bound h l -> l <> l'.
Proof. introv B F E. subst. apply* fresh_not_bound. Qed.

Lemma fresh_not_indom : forall h l f,
  fresh h l -> indom h l f -> False.
Proof. intros. apply* fresh_not_bound. apply* indom_bound. Qed.

Lemma fresh_indom_neq : forall h l l' f, 
  fresh h l' -> indom h l f -> l <> l'.
Proof. introv B F E. subst. apply* fresh_not_indom. Qed.

Lemma fresh_not_binds : forall h l f v,
  fresh h l -> binds h l f v -> False.
Proof. intros. apply* fresh_not_indom. applys* binds_indom. Qed.

Lemma fresh_binds_neq : forall h l l' f v, 
  fresh h l' -> binds h l f v -> l <> l'.
Proof. introv B F E. subst. apply* fresh_not_binds. Qed.

(** Preservation of fresh *)

Lemma fresh_write : forall l' h l f v,
  fresh h l' -> l <> l' -> fresh (write h l f v) l'.
Proof. 
  introv [L B] N. split. auto.
  intros B'. lets (f'&v'&R): bound_binds B'.
  lets [(?&?&?)|(?&?)]: binds_write_inv R.
    false.
    apply* not_bound_binds.
Qed.

Lemma fresh_write_weaken : forall l' h l f v,
  fresh (write h l f v) l' -> fresh h l'.
Proof.
  introv [L B]. split. auto.
  intros [f' B']. apply B. eapply indom_bound.
  apply* indom_write.
Qed.


(**************************************************************)
(** ** Hints for proving freshness goals *)

Hint Extern 1 (fresh _ ?l) => 
  match goal with H: fresh _ ?l |- _ => 
    apply (fresh_write_weaken H) end.

Hint Resolve fresh_binds_neq.

Hint Extern 1 (_ <> _ :> ref) => congruence.


(**************************************************************)
(** ** Tactics *)

(*--------------------------------------------------------------*)

(** The following tactic strengthens [congruence] by making it
    able to bruteforce a goal that concludes on a disjunction *)

Ltac congruence_on_disjunction :=
  let rec go tt := 
    match goal with
    | |- _ \/ _ => first [ left; go tt | right; go tt ]
    | |- _ => congruence
    end in
  go tt.

Lemma congruence_on_disjunction_demo : forall (l l' : nat), 
  l <> l' -> (l <> l' \/ l' <> l \/ l <> l').
Proof. intros. try congruence. congruence_on_disjunction. Qed.

(*--------------------------------------------------------------*)

(** The tactic [indom_simpl_step] simplifies a goal of the
    form [indom (write h l f v) l' f'] by handling the case 
    where [l'] is syntactically [l] and [f'] is syntactically [f],
    and otherwise turning the goal into [indom h l' f']. 
    It also handles the [write_fields]. Note that you might 
    need to do a case analysis on [l = l'] and [f = f'] before 
    calling this tactic. It also handles the empty heap.  *)

Ltac indom_simpl_step :=
  match goal with
  | |- indom (write ?h ?l ?f _) ?l ?f =>
     apply indom_write_eq
  | |- indom (write_fields _ _ nil) _ _ =>  
     rewrite write_fields_nil; indom_simpl_step 
  | |- indom (write_fields _ _ (_::_)) _ _ =>  
     rewrite write_fields_cons; indom_simpl_step
  | |- indom (write ?h ?l' ?f' _) ?l ?f =>
     apply indom_write
  | |- indom ?h _ _ => 
     let P := get_head h in progress (unfold P); indom_simpl_step
  | |- _ =>
     progress (unfolds); indom_simpl_step 
  end.

(** The tactic [indom_simpl] iterates [indom_simpl_step]. *)

Tactic Notation "indom_simpl" :=
  repeat indom_simpl_step.
Tactic Notation "indom_simpl" "~" :=
  indom_simpl; auto_tilde.
Tactic Notation "indom_simpl" "*" :=
  indom_simpl; auto_star.


(*--------------------------------------------------------------*)

(** The tactic [binds_simpl_step] simplifies goal of the form
    [binds (write h l f v) f' l' v'] by handling the case where
    [l'] is syntactically [l] and [f'] is syntactically [f],
    and otherwise discarding the write, producing [l <> l' \/ f <> f']
    as subgoal and trying to prove it using [congruence]. 
    The tactic also handles [write_fields] in the case where [l <> l']. *)
  
Ltac binds_simpl_step :=
  match goal with
  | |- binds (write ?h ?l ?f _) ?l ?f _ =>
     apply binds_write_eq
  | |- binds (write_fields ?h ?l' ?fvs') ?l _ _ =>  
     let F := fresh in
     assert (F : l <> l');
       [ try congruence 
       | apply binds_write_fields_neq; [ clear F | apply F ]]
  | |- binds (write ?h ?l' ?f' _) ?l ?f _ =>
     let F := fresh in
     assert (F : l <> l' \/ f <> f');
       [ try congruence_on_disjunction 
       | apply binds_write_neq; [ clear F | apply F ]]
  | |- binds ?h _ _ _ => 
     let P := get_head h in progress (unfold P); binds_simpl_step
  | |- _ => 
     progress (unfolds); binds_simpl_step
  end.

(** The tactic [binds_simpl] iterates [binds_simpl_step]. *)

Tactic Notation "binds_simpl" :=
  repeat binds_simpl_step.
Tactic Notation "binds_simpl" "~" :=
  binds_simpl; auto_tilde.
Tactic Notation "binds_simpl" "*" :=
  binds_simpl; auto_star.


(*--------------------------------------------------------------*)

(** The tactic [binds_case H] helps extracting information from an
    assumption [H] of the form [binds (write h l' f' v') l f v].
    If [l'] is syntactically [l] and [f'] is syntactically [f],
    then the tactic simplifies [H] to [v' = v]. Otherwise, if
    [l' <> l] or [f' <> f] is provable using [congruence], then
    the tactic simplifies [H] to [binds h l f v]. Otherwise, the
    tactic performs the case analysis and generates two subgoals,
    one corresponding to each case. 
    The tactic also handles [write_fields] by unfolding the head
    write in write_fields, if any. It also handles the empty heap. *)

Ltac binds_case_step H :=
  match type of H with 
  | binds (write ?h ?l ?f _) ?l ?f _ =>
     apply binds_write_eq_inv in H (*; try solve [ congruence ] *)
  | binds (write ?h ?l' ?f' ?v') ?l ?f ?v =>
     first [
       let F := fresh in let H' := fresh in
       assert (F : l <> l' \/ f <> f');
         [ congruence_on_disjunction 
         | rename H into H';
           lets H: (binds_write_neq_inv H' F); clear F H' ]
     | let H' := fresh in rename H into H'; 
       let N := fresh "N" in let E1 := fresh "E1" in
       let E2 := fresh "E2" in let E3 := fresh "E3" in
       destruct (binds_write_inv H') as [(E1&E2&E3)|(N&H)]; 
         [ clear H'; try solve [ false; congruence ];
           try subst_hyp E1; try subst_hyp E2; try subst_hyp E3
         | clear H' ]
     ]
  | binds (write_fields _ _ nil) _ _ _ =>  
     rewrite write_fields_nil in H
  | binds (write_fields _ _ (_::_)) _ _ _ =>  
     rewrite write_fields_cons in H; binds_case_step H
  | binds (write_fields _ _ _) _ _ _ =>  
     fail 2 "list given to write_fields should not be abstract"
  | binds empty_heap _ _ _ =>
     false (not_binds_empty H)
  | binds ?h _ _ _ =>
     let P := get_head h in progress (unfold P in H); binds_case_step H
  end.

Tactic Notation "binds_case" hyp(H) :=
  binds_case_step H.
Tactic Notation "binds_case" "~" hyp(H) :=
  binds_case H; auto_tilde.
Tactic Notation "binds_case" "*" hyp(H) :=
  binds_case H; auto_star.

(** The tactic [binds_cases] iterates [binds_case] *)

Tactic Notation "binds_cases" hyp(H) :=
  repeat (binds_case H).
Tactic Notation "binds_cases" "~" hyp(H) :=
  binds_cases H; auto_tilde.
Tactic Notation "binds_cases" "*" hyp(H) :=
  binds_cases H; auto_star.

