Set Implicit Arguments.
Require Export LibCore.

Generalizable Variable A B P.
 
(** [Decidable P] asserts that there exists a boolean
    value indicating whether [P] is true. The definition
    is interesting when this boolean is computable and
    can lead to code extraction. *)

Class Decidable (P:Prop) := make_Decidable {
  decide : bool;
  decide_spec : decide = isTrue P }.

Implicit Arguments decide [[Decidable]].
Extraction Inline decide.

Lemma Decidable_dec : forall (P:Prop) {H: Decidable P} (A:Type) (x y:A),  
  exists Q : {P}+{~P},
  (if decide P then x else y) = (if Q then x else y).
Proof.
  intros. exists (classicT P). 
  rewrite decide_spec.
  tautotest P; case_if as C; case_if as C'; 
   rew_unreflect in C; auto*; false*.
Qed.

(** Extending the [case_if] tactic to support [if decide] *)

Ltac case_if_on_tactic E Eq ::=
  match E with
  | decide ?P => 
      let Q := fresh in let E := fresh in
      forwards (Q&E): (@Decidable_dec P); 
      rewrite E in *; clear E; destruct Q 
  | _ =>
    match type of E with
    | {_}+{_} => destruct E as [Eq|Eq]; try subst_hyp Eq
    | _ => let X := fresh in 
           sets_eq <- X Eq: E;
           destruct X
    end
  end; case_if_post.

(** For example, [True] is a decidable proposition *)

Instance True_decidable : Decidable True.
Proof. applys make_Decidable true. rewrite~ isTrue_True. Qed.

Lemma Decidable_demo : 
  (if decide True then O else S O) = O.
Proof.
  dup.
  (* tactic proof *)
  case_if.
    auto.
    false*.
  (* manual proof *)
  rewrite decide_spec. case_if as C; rew_unreflect in C.
    auto.
    false.
Qed.

(** [Comparable A] asserts that there exists a decidable
    equality over values of type [A] *)

Class Comparable (A:Type) := make_Comparable {
  comparable : forall (x y:A), Decidable (x = y) }.

Hint Resolve @comparable : typeclass_instances.

Lemma prove_Comparable : forall A (f:A->A->bool),
  (forall x y, (istrue (f x y)) <-> (x = y)) ->
  Comparable A.
Proof.
  introv H. constructors. intros. 
  applys make_Decidable (f x y). 
  extens. rewrite istrue_isTrue. apply H.
Qed.

Extraction Inline comparable.
Extraction Inline prove_Comparable.

(** Example: comparison over [nat] *)

Fixpoint nat_compare (x y : nat) :=
  match x, y with
  | O, O => true
  | S x', S y' => nat_compare x' y'
  | _, _ => false
  end.

Instance nat_comparable : Comparable nat.
Proof.
  applys (@prove_Comparable nat) nat_compare. (* todo: remove type annot *)
  induction x; destruct y; simpl.
  auto*.
  auto_false.
  auto_false.
  asserts_rewrite ((S x = S y) = (x = y)).
    extens. iff; math.
  auto*.
Qed.

Definition nat_comparable_demo (x y : nat) :=
  if decide (x = y) then O else S O.

Lemma nat_comparable_demo_spec : 
  nat_comparable_demo O (S O) = S O.
Proof.
  unfold nat_comparable_demo.
  case_if. auto. math. 
Qed.

(** The extraction of [decide (x = y)] when [x y : nat]
    is indeed [nat_compare x y]. *)

Extraction Inline nat_comparable.
Extraction nat_comparable_demo.


(** Model of heaps --the one we already have in Shared.v *)

Parameter heap : Type -> Type -> Type.
Parameter indom : forall K V, heap K V -> K -> Prop.

(** Implementation of a boolean [indom] function *)

Generalizable Variable K.

Parameter indom_dec : forall `{Comparable K} V, heap K V -> K -> bool.
Parameter indom_dec_spec : forall `{Comparable K} V (h:heap K V) k, 
  indom_dec h k = isTrue (indom h k).

(** Registering [indom_dec] to decide [indom] *)

Instance indom_decidable : forall `{Comparable K} V (h:heap K V) k,
  Decidable (indom h k).
Proof.
  intros. applys make_Decidable (indom_dec h k).
  applys indom_dec_spec.
Qed.

(** Demo *)

Parameter value : Type.

Definition indom_demo (h:heap nat value) k :=
  if decide (indom h k) then O else S O.

(** Extraction of [decide (indom h k)] is
    [indom_dec nat_compare h k] *)

Extraction Inline indom_decidable.
Extraction indom_demo.





Definition indom_bool h l f : bool :=
  Heap.indom_bool h (Ref l f).

Definition indom_bool_spec h l f :
  indom_bool h l f = isTrue (indom h l f).
Proof. introv; eapply Heap.indom_bool_spec. Defined.
