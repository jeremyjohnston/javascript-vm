Set Implicit Arguments.
Require Export LibTactics LibCore LibString LibSet.
Generalizable Variables A B.
Require Export LibProd.



(**************************************************************)
(** ** LATER: move to LibTactics *)

Ltac decompose_base X I :=
  gen ltac_mark; gen X; intros X;
  let Y := fresh in set (Y:=X); destruct X as I; rename Y into X;
  intro_until_mark.

Tactic Notation "decompose" ident(E) "as" simple_intropattern(I) :=
  decompose_base E I.


(**************************************************************)
(** ** LATER: move to LibSet *)

Section Instances.
Variables (A:Type).

Global Instance incl_union_r_from_incl_union_l :
  Incl_union_l (T:=set A).
Admitted.
Global Instance set_incl_union_l :
  Incl_refl (T:=set A).
Admitted.
Global Instance set_incl_refl :
  Incl_trans (T:=set A).
Admitted.
End Instances.

Generalizable Variable T.

Lemma union_idem_r : forall A (E F:set A),
  E \u F \u F = E \u F.
Admitted.

Class In_incl `{BagIn A T} `{BagIncl T} :=
  { in_incl : forall E F, (forall x, x \in E -> x \in F) -> E \c F }.

Global Instance set_in_incl_inst : In_incl (A:=A) (T:=set A).
Proof. Admitted.


(**************************************************************)
(** ** LATER: move to LibList *)

Lemma list_case_last : forall A (l : list A),
  l = nil \/ exists x l', l = l'&x.
Proof. skip. Qed.

Lemma list_ind_last : forall (A : Type) (P : list A -> Prop),
  P nil ->
  (forall (a : A) (l : list A), P l -> P (l & a)) ->
  forall l : list A, P l.
Proof.
  intros. induction_wf IH: (measure_wf (@LibList.length A)) l.
  skip.
Qed.

(* Stuff moved from JsSafety.v *)

Axiom last_eq_last_inv : forall A a1 a2 (l1 l2:list A),
  l1 & a1 = l2 & a2 -> l1 = l2 /\ a1 = a2.

Axiom case_last : forall A (l:list A), 
  l = nil \/ exists x l', l = l' & x.

Axiom Forall_last_inv : forall A (P:A->Prop) l x, 
  Forall P (l & x) ->
  P x /\ Forall P l. 
(* todo: change hypotheses in forall_last *)


(**************************************************************)
(** ** LATER: move to LibReflect *)

Global Instance and_decidable :
  forall P1 P2, Decidable P1 -> Decidable P2 ->
  Decidable (P1 /\ P2).
Proof.
introv D1 D2. applys decidable_make (decide P1 && decide P2).
rewrite isTrue_and. repeat rewrite decide_spec. auto.
Qed.


(**************************************************************)
(** ** LATER: move to LibFix *)

Require Import LibFix.

Definition FixFun4Mod B {IB:Inhab B} (E:binary B)
  A1 A2 A3 A4 (F:(A1->A2->A3->A4->B)->(A1->A2->A3->A4->B)) :=
  curry4 (FixFunMod E (fun f' => uncurry4 (F (curry4 f')))).

Definition FixFun4 B {IB:Inhab B} := FixFun4Mod eq.

Lemma FixFun4_fix_partial : forall A1 A2 A3 A4 (R:binary (A1*A2*A3*A4)) (P:A1->A2->A3->A4->Prop)
  B {IB:Inhab B} F (f:A1->A2->A3->A4->B), 
  f = FixFun4 F -> wf R -> 
  (forall x1 x2 x3 x4 f1 f2, P x1 x2 x3 x4 ->   
    (forall y1 y2 y3 y4, P y1 y2 y3 y4 -> R (y1,y2,y3,y4) (x1,x2,x3,x4) -> f1 y1 y2 y3 y4 = f2 y1 y2 y3 y4) ->
     F f1 x1 x2 x3 x4 = F f2 x1 x2 x3 x4) ->
  (forall x1 x2 x3 x4, P x1 x2 x3 x4 -> f x1 x2 x3 x4 = F f x1 x2 x3 x4).
Admitted.

Implicit Arguments FixFun4_fix_partial [A1 A2 A3 A4 B IB F f].

(**************************************************************)
(** ** move to LibList (or LibReflect?) *)

(* LibList.mem does not use `decide' but `isTrue' and is thus extracted
   classically. *)
Fixpoint mem_decide (A : Type) `{Comparable A} (x : A) (l : list A) {struct l} := (* I don't kow why, but by default the structural decrease of the fix is on `{Comparable A}. *)
  match l with
  | nil => false
  | y::l' => ifb x = y then true else mem_decide x l'
  end.

Lemma mem_decide_eq_mem : forall A (H : Comparable A) (x : A) l,
  mem_decide x l = LibList.mem x l.
Proof.
  induction l.
   auto.
   simpl. case_if.
     rewrite~ eqb_eq.
     rewrite~ eqb_neq. rewrite~ neutral_l_or.
Qed.

Global Instance In_decidable : forall A : Set,
  Comparable A ->
  forall (x : A) l, Decidable (In x l).
Proof.
  introv CA. intros.
  applys decidable_make (mem_decide x l).
  rewrite mem_decide_eq_mem.
  induction l.
    simpl. rew_refl~.
    tests: (a = x); simpl; rew_refl.
      rewrite eqb_self. simpl. reflexivity.
      do 2 rewrite~ eqb_neq. rewrite~ IHl.
Qed.

(**************************************************************)
(** ** move to LibList *)


Section LogicList.
Variables A B C D : Type.

(** Similar to [Forall2] except that it relates four lists *)

Inductive Forall4 (P : A -> B -> C -> D -> Prop) 
  : list A -> list B -> list C -> list D -> Prop :=
  | Forall4_nil :
      Forall4 P nil nil nil nil
  | Forall4_cons : forall l1 l2 l3 l4 x1 x2 x3 x4, 
      P x1 x2 x3 x4 -> Forall4 P l1 l2 l3 l4 -> 
      Forall4 P (x1::l1) (x2::l2) (x3::l3) (x4::l4).
End LogicList.

Section ListProp.
Variables A B C D : Type.
Lemma Forall_trans : forall P Q : A -> Prop,
  (forall a, P a -> Q a) ->
  forall la, Forall P la ->
    Forall Q la.
Proof.
  introv I. intros.
  induction H.
    apply Forall_nil.
    apply~ Forall_cons.
Qed.
  
Lemma Forall4_trans : forall P Q : A -> B -> C -> D -> Prop,
  (forall a b c d, P a b c d -> Q a b c d) ->
  forall la lb lc ld, Forall4 P la lb lc ld ->
    Forall4 Q la lb lc ld.
Proof.
  introv I. intros.
  induction H.
    apply Forall4_nil.
    apply~ Forall4_cons.
Qed.
  
Lemma Forall3_trans : forall P Q : A -> B -> C -> Prop,
  (forall a b c, P a b c -> Q a b c) ->
  forall la lb lc, Forall3 P la lb lc->
    Forall3 Q la lb lc.
Proof.
  introv I. intros.
  induction H.
    apply Forall3_nil.
    apply~ Forall3_cons.
Qed.

(* FIXME: I do not know if those lemmas are really expressed in a
   natural and practical way. *)

Lemma Forall4_remove1 : forall P : B -> C -> D -> Prop,
  forall la lb lc ld,
  Forall4 (fun (_ : A) => P) la lb lc ld ->
  Forall3 P lb lc ld.
Proof.
  introv F4.
  induction F4.
    constructor.
    constructor~.
Qed.

Lemma Forall3_remove1 : forall P : B -> C -> Prop,
  forall la lb lc,
  Forall3 (fun (_ : A) => P) la lb lc ->
  Forall2 P lb lc.
Proof.
  introv F3.
  induction F3.
    constructor.
    constructor~.
Qed.

Lemma Forall3_permute12 : forall P : A -> B -> C -> Prop,
  forall la lb lc,
  Forall3 P la lb lc ->
  Forall3 (fun b a => P a b) lb la lc.
Proof.
  introv F3.
  induction F3.
    constructor.
    constructor~.
Qed.

Lemma Forall4_permute12 : forall P : A -> B -> C -> D -> Prop,
  forall la lb lc ld,
  Forall4 P la lb lc ld ->
  Forall4 (fun b a => P a b) lb la lc ld.
Proof.
  introv F4.
  induction F4.
    constructor.
    constructor~.
Qed.

Lemma Forall3_last_inv : forall (P : A -> B -> C -> Prop) l1 l2 l3 x1,
  Forall3 P (l1 & x1) l2 l3 ->
  exists r2 x2 r3 x3, l2 = r2 & x2 /\ l3 = r3 & x3
    /\ P x1 x2 x3 /\ Forall3 P l1 r2 r3.
Proof.
  introv H. sets_eq l': (l1&x1). gen l1 x1.
  induction H; intros; subst.
  false* nil_eq_last_inv.
  destruct l0; rew_app in EQl'; inverts EQl'.
    inverts H0. exists (@nil B) x2 (@nil C) x3. splits*. constructor.
    forwards~ (r2'&x2'&r3'&x3'&?&?&?): IHForall3. subst.
     exists (x2::r2') x2' (x3::r3') x3'. splits*. constructor*.
Qed.

End ListProp.


(**************************************************************)
(** ** move to LibReflect *)

Ltac case_if_on_tactic_core E Eq ::=
  match E with
  | @decide ?P ?M => 
      let Q := fresh in let Eq := fresh in
      forwards (Q&Eq): (@Decidable_dec P M); 
      rewrite Eq in *; clear Eq; destruct Q 
  | _ =>
    match type of E with
    | {_}+{_} => destruct E as [Eq|Eq]; try subst_hyp Eq
    | _ => let X := fresh in 
           sets_eq <- X Eq: E;
           destruct X
    end
  end.

