Set Implicit Arguments.
Require Import LibLogic LibHeap.
Require Export JsSyntax. 
Implicit Type h : heap.
Implicit Type l : loc.
Implicit Type f : field.


(**************************************************************)
(** ** Inhabitants and comparison functions for base types *)

(** Inhabitants *)

Global Instance loc_inhab : Inhab loc.
Proof. apply (prove_Inhab loc_null). Qed.

Global Instance value_inhab : Inhab value.
Proof. apply (prove_Inhab value_undef). Qed.

Global Instance field_inhab : Inhab field.
Proof. apply (prove_Inhab field_proto). Qed.

Global Instance ref_inhab : Inhab ref.
Proof. apply (prove_Inhab (Ref arbitrary arbitrary)). Qed.

(** Comparison functions *)

Definition loc_compare (l1 l2 : loc) :=
  match l1, l2 with
  | loc_normal n1, loc_normal n2 => decide (n1 = n2)
  | loc_null, loc_null => true
  | loc_eval, loc_eval => true
  | loc_scope, loc_scope => true
  | loc_global, loc_global => true
  | loc_obj_proto, loc_obj_proto => true
  | loc_func_proto, loc_func_proto => true
  | loc_eval_proto, loc_eval_proto => true
  | _, _ => false
  end.

Global Instance loc_comparable : Comparable loc.
Proof.
  applys (comparable_beq loc_compare). intros x y.
  destruct x; destruct y; simpl; rew_refl; iff;
   tryfalse; auto; try congruence.
Qed.

Definition field_compare (f1 f2 : field) :=
  match f1, f2 with
  | field_normal s1, field_normal s2 => decide (s1 = s2)
  | field_proto, field_proto => true
  | field_body, field_body => true
  | field_scope, field_scope => true
  | field_this, field_this => true
  | _, _ => false
  end.

Global Instance field_comparable : Comparable field.
Proof.
  applys (comparable_beq field_compare). intros x y.
  destruct x; destruct y; simpl; rew_refl; iff;
   tryfalse; auto; try congruence.
Qed.

Definition ref_compare r1 r2 :=
  match r1, r2 with Ref l1 f1, Ref l2 f2 =>
    decide (l1 = l2) && decide (f1 = f2) end.

Global Instance ref_comparable : Comparable ref.
Proof.
  applys (comparable_beq ref_compare). intros x y.
  destruct x; destruct y; simpl; rew_refl.
  iff M; inverts~ M.
Qed.

Global Instance number_comparable : Comparable number.
Proof. Admitted.
(* ARTHUR: use Rcompare to implement this *)

Definition value_compare (v1 v2 : value) :=
  match v1, v2 with
  | value_undef, value_undef => true
  | value_bool b1, value_bool b2 => decide (b1 = b2)
  | value_number n1, value_number n2 => decide (n1 = n2)
  | value_string s1, value_string s2 => decide (s1 = s2)
  | value_loc l1, value_loc l2 => decide (l1 = l2)
  | _, _ => false
  end.
