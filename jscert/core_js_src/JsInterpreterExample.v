Set Implicit Arguments.
Require Import JsSemantics JsWfAux JsInterpreter.
Require Import LibFix LibList.

Section Example.

(* NEWSYNTAX "undef" is not valid syntax, so I use skip *)
Definition expr_undef := expr_skip.


Definition seq l :=
  match fold_right
      (fun e s =>
        match s with
        | None => Some e
        | Some e' => Some (expr_seq e e')
        end)
      None l
  with
  | None => expr_undef
  | Some a => a
  end.

Local Notation "[ ]" := nil : list_scope.
Local Notation "[ a ; .. ; b ]" := (a :: .. (b :: []) ..) : list_scope.

Parameter max_int : nat.

(* (* ------ prog1.js ------ *)
convert = function(n) { return (n( (function(n) { return n + 1 }))) (0)  };

succ = function(n) { return function(f) { return function(x) {
    return n(f)(f(x))
  }}};

zero = function(f) { return function(x) { return x } };

plus = function(x, y){ return x(succ)(y) }};

var one = succ(zero);

convert(plus(one, one))
*)

Definition prog1 :=
  seq [
    expr_assign (expr_variable "convert") None (expr_function None ["n"%string] (
      expr_call (expr_call (expr_variable "n") [expr_function None ["n"%string] (
        expr_binary_op (expr_variable "n") binary_op_add (
          expr_literal (literal_number (number_of_int 1)))
        )]) [expr_literal (literal_number (number_of_int 0))]
    ));
    expr_assign (expr_variable "succ") None (expr_function None ["n"%string] (expr_function None ["f"%string] (expr_function None ["x"%string] (
      expr_call (expr_call (expr_variable "n") [expr_variable "f"])
        [expr_call (expr_variable "f") [expr_variable "x"]]
    ))));
    expr_assign (expr_variable "zero") None (expr_function None ["f"%string] (expr_function None ["x"%string] (expr_variable "x")));
    expr_assign (expr_variable "plus") None (expr_function None ["x"%string ; "y"%string] (
      expr_call (expr_call (expr_variable "x") [expr_variable "succ"]) [expr_variable "y"]));
    expr_var_decl "one"
      (Some (expr_call (expr_variable "succ") [expr_variable "zero"]));
    expr_call (expr_variable "convert")
      [expr_call (expr_variable "plus") [expr_variable "one" ; expr_variable "one"]]
  ].

Definition computation1 := run max_int init_heap init_scope prog1.

(* (* ------ prog2.js ------ *)
var id = function(x) { return x }; (* To deference the final value. *)

var f = function() {
  this.x = 0;
  this.g = function() { this.x = 1; return this };
  void 0 
  };

var h = function() { };
h.prototype = new f();

var test = new h();

id(test.g().x)
*)

Definition expr_var_decl' s e := 
  expr_var_decl s (Some e).
Definition expr_assign' e1 e2 :=
  expr_assign e1 None e2.

Definition prog2 := seq [
  expr_var_decl' "id" (expr_function None ["x"%string] (expr_variable "x"));
  expr_var_decl' "f" (expr_function None [] (
    seq [
      expr_assign' (expr_member expr_this "x") (expr_literal (literal_number (number_of_int 0)));
      expr_assign' (expr_member expr_this "g") (expr_function None [] (
        seq [
          expr_assign' (expr_member expr_this "x") (expr_literal (literal_number (number_of_int 1)));
          expr_this
        ]
      ));
      expr_undef ]
    ));
  expr_var_decl' "h" (expr_function None [] (seq []));
  expr_assign' (expr_member (expr_variable "h") "prototype") (
    expr_new (expr_variable "f") []);
  expr_var_decl' "test" (expr_new (expr_variable "h") []);

  expr_call (expr_variable "id") [
    expr_member (expr_call (expr_member (expr_variable "test") "g") [])
      "x"]
  ].

Definition computation2 := run max_int init_heap init_scope prog2.

(* (* ------ prog3.js ------ *)
Object.prototype.x = 42;
var x = 24;
var f = function (){ return x; };
f()
*)

Definition prog3 := seq [
  (* expr_assign (expr_member (expr_member (expr_literal (value_loc loc_global)) "prototype") "x") (expr_literal (literal_number (number_of_int 24)));*) (* This is not correct and the initial heap had to be modified to be able to use this example. *)
  expr_var_decl' "x" (expr_literal (literal_number (number_of_int 24)));
  expr_var_decl' "f" (expr_function None [] (expr_variable "x"));
  expr_call (expr_variable "f") []
  ].

Definition computation3 := run max_int (write init_heap loc_obj_proto (field_normal "x") (value_number (number_of_int 42))) init_scope prog3.

End Example.

(* Here stands some commands to extract relatively correctly the interpreter to Ocaml. *)
Extraction Language Ocaml.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlString.

(* Optimal fixpoint. *)
Extraction Inline FixFun3 FixFun3Mod FixFun4 FixFun4Mod FixFunMod curry3 uncurry3 curry4 uncurry4.
(* As classical logic statements are now unused, they should not be extracted
   (otherwise, useless errors will be launched). *)
Extraction Inline epsilon epsilon_def classicT arbitrary indefinite_description Inhab_witness Fix isTrue.

(* number *)
Require Import ExtrOcamlZInt.
Extract Inductive Fappli_IEEE.binary_float => float [
  "(fun s -> if s then (0.) else (-0.))"
  "(fun s -> if s then infinity else neg_infinity)"
  "nan"
  "(fun (s, m, e) -> let f = ldexp (float_of_int m) e in if s then f else -.f)"
].
Extract Constant number_comparable => "(=)".
Extract Constant number_add => "(+.)".
Extract Constant number_mult => "( *. )".
Extract Constant number_div => "(/.)".
Extract Constant number_of_int => float_of_int.
(* The following functions make pattern matches with floats and will thus be removed. *)
Extraction Inline Fappli_IEEE.Bplus Fappli_IEEE.binary_normalize Fappli_IEEE_bits.b64_plus.
Extraction Inline Fappli_IEEE.Bmult Fappli_IEEE.Bmult_FF Fappli_IEEE_bits.b64_mult.
Extraction Inline Fappli_IEEE.Bdiv Fappli_IEEE_bits.b64_div.

(* fresh_for *)
Extract Constant fresh_for => fresh_for_list.

(* Some constants *)
Extract Constant max_int => max_int.
Extract Constant Mnostuck => true.

Extraction "interpreter.ml" fresh_for_list
  computation1 computation2 computation3.

