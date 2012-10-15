Set Implicit Arguments.
Require Export Shared.
Require Export Ascii String.
Require Export LibTactics LibLogic LibReflect LibList
  LibOperation LibStruct LibNat LibEpsilon LibFunc LibHeap.
Require Fappli_IEEE Fappli_IEEE_bits.


(************************************************************)
(************************************************************)
(************************************************************)
(************************************************************)
(** * Javascript *)

(************************************************************)
(** ** Strings *)

Definition char := ascii.
Definition string := list char.

Fixpoint string_to_char_list (s:String.string) : string :=
  match s with
    | EmptyString => nil
    | String a s' => a :: (string_to_char_list s')
  end.

Coercion string_to_char_list : String.string >-> string.

Fixpoint string_eq_bool s1 s2 :=
  match s1,s2 with
    | nil, nil => true
    | c1::t1, c2::t2 => if ascii_dec c1 c2 then string_eq_bool t1 t2 else false
    | _, _ => false
  end.

Instance string_decidable : forall s1 s2 : string, Decidable (s1 = s2).
Proof.
  introv. applys decidable_make (string_eq_bool s1 s2). extens.
  iff H.
    inductions s1.
      destruct s2; tryfalse. rew_refl~.
      destruct s2; tryfalse. simpls. cases_if~. forwards~ Ht: IHs1 s2. rew_refl in Ht. rewrites~ Ht.
    inductions s1.
      destruct* s2. rew_refl in H. false H.
      rew_refl in H. destruct* s2; tryfalse. simpls. cases_if~. injects H. applys IHs1. rew_refl~.
Qed.
                                                                                                
Open Scope string_scope.

(**************************************************************)
(** ** Numerical literals *)

Definition number : Type := 
  Fappli_IEEE_bits.binary64.

Definition number_of_int : int -> number := 
  Fappli_IEEE_bits.b64_of_bits.

Definition number_add : number -> number -> number :=
  Fappli_IEEE_bits.b64_plus Fappli_IEEE.mode_NE.

Definition number_mult : number -> number -> number :=
  Fappli_IEEE_bits.b64_mult Fappli_IEEE.mode_NE.

Definition number_div : number -> number -> number :=
  Fappli_IEEE_bits.b64_div Fappli_IEEE.mode_NE.


(**************************************************************)
(** ** Datatypes *)

(** Binary operators *)
(** Only allow those which can be used with assignment *)
(** * / % + - << >> >>> & ^ | *)

Inductive binary_op :=
  | binary_op_add
  | binary_op_mult
  | binary_op_div.

(** Comparison operators *)

Inductive comparison_op :=
  | comparison_op_equal
  | comparison_op_instanceof
  | comparison_op_in.

(* Unary operator *)

Inductive unary_op :=
  | unary_op_not
  | unary_op_delete
  | unary_op_typeof
  | unary_op_pre_incr
  | unary_op_post_incr
  | unary_op_pre_decr
  | unary_op_post_decr
  | unary_op_void.

(** Grammar of literals *)

Inductive literal :=
  | literal_null : literal
  | literal_bool : bool -> literal
  | literal_number : number -> literal 
  | literal_string : string -> literal.

(** Grammar of expressions *)

Inductive expr :=
  | expr_this : expr
  | expr_variable : string -> expr
  | expr_literal : literal -> expr
  | expr_object : list (string * expr) -> expr
  | expr_function : option string -> list string -> expr -> expr 
  | expr_access : expr -> expr -> expr
  | expr_member : expr -> string -> expr
  | expr_new : expr -> list expr -> expr
  | expr_call : expr -> list expr -> expr
  | expr_unary_op : unary_op -> expr -> expr
  | expr_binary_opary_op : expr -> binary_op -> expr -> expr
  | expr_and : expr -> expr -> expr
  | expr_or : expr -> expr -> expr
  | expr_assign : expr -> option binary_op -> expr -> expr
  | expr_seq : expr -> expr -> expr
  | expr_var_decl : string -> option expr -> expr
  | expr_if : expr -> expr -> option expr -> expr
  | expr_while : expr -> expr -> expr
  | expr_with : expr -> expr -> expr
  | expr_skip : expr.

Coercion expr_literal : literal >-> expr.

(* To be move to JsSemantics *)

(** Locations (address of objects) *)

Inductive loc :=
  | loc_normal : nat -> loc
  | loc_null : loc
  | loc_scope : loc
  | loc_global : loc
  | loc_eval : loc
  | loc_obj_proto : loc
  | loc_func_proto : loc
  | loc_eval_proto : loc.

(** Field names *)

Inductive field :=
  | field_normal : string -> field
  | field_proto : field
  | field_body : field
  | field_scope: field
  | field_this : field.

(** The particular "prototype" field name *)

Definition field_normal_prototype := 
  field_normal "prototype".

(** Reference: pair of a location and a field *)

Inductive ref := 
  | Ref : loc -> field -> ref.

(** Scope chain *)

Definition scope := list loc.

(** Grammar of values *)

Inductive value :=
  | value_undef : value 
  | value_bool : bool -> value
  | value_number : number -> value 
  | value_string : string -> value
  | value_loc : loc -> value
  | value_scope : scope -> value
  | value_body : list string -> expr -> value.

(** Result of an evaluation: a value or a reference *)

Inductive result :=
  | result_value : value -> result
  | result_ref : ref -> result.

(** Coercions *)

Coercion field_normal : string >-> field.
Coercion value_number : number >-> value.
Coercion value_string : string >-> value.
Coercion value_loc : loc >-> value.
Coercion result_value : value >-> result.
Coercion result_ref : ref >-> result.


(**************************************************************)
(** ** Heaps *)

(** Heaps are based on the "heap" typed defined in [Shared.v].
    The values [heap_write], [heap_read] and [heap_binds]
    and [indom] are also defined in [Shared.v] *)

(** Definition heap as heap from references to value.*)

Module Heap := LibHeap.HeapList.

Definition heap := Heap.heap ref value.

(* Extraction of the syntax *)
Extraction Language Ocaml.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.

(* num *)
Require Import ExtrOcamlZInt.
Extract Inductive Fappli_IEEE.binary_float => float [
  "(fun s -> if s then (0.) else (-0.))"
  "(fun s -> if s then infinity else neg_infinity)"
  "nan"
  "(fun (s, m, e) -> let f = ldexp (float_of_int m) e in if s then f else -.f)"
].
(* The following functions make pattern matches with floats and will thus be removed. *)
Extraction Inline Fappli_IEEE.Bplus Fappli_IEEE.binary_normalize Fappli_IEEE_bits.b64_plus.
Extraction Inline Fappli_IEEE.Bmult Fappli_IEEE.Bmult_FF Fappli_IEEE_bits.b64_mult.
Extraction Inline Fappli_IEEE.Bdiv Fappli_IEEE_bits.b64_div.

Extraction "syntax.ml" expr.

