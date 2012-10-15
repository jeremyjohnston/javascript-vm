type __ = Obj.t

val negb : bool -> bool

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

type comparison =
| Eq
| Lt
| Gt

type compareSpecT =
| CompEqT
| CompLtT
| CompGtT

val compareSpec2Type : comparison -> compareSpecT

type 'a compSpecT = compareSpecT

val compSpec2Type : 'a1 -> 'a1 -> comparison -> 'a1 compSpecT

type 'a sig0 =
  'a
  (* singleton inductive, whose constructor was exist *)

val plus : int -> int -> int

val nat_iter : int -> ('a1 -> 'a1) -> 'a1 -> 'a1

type reflect =
| ReflectT
| ReflectF

val iff_reflect : bool -> reflect

module type TotalOrder' = 
 sig 
  type t 
 end

module MakeOrderTac : 
 functor (O:TotalOrder') ->
 sig 
  
 end

module MaxLogicalProperties : 
 functor (O:TotalOrder') ->
 functor (M:sig 
  val max : O.t -> O.t -> O.t
 end) ->
 sig 
  module Private_Tac : 
   sig 
    
   end
 end

module Pos : 
 sig 
  type t = int
  
  val succ : int -> int
  
  val add : int -> int -> int
  
  val add_carry : int -> int -> int
  
  val pred_double : int -> int
  
  val pred : int -> int
  
  val pred_N : int -> int
  
  type mask =
  | IsNul
  | IsPos of int
  | IsNeg
  
  val mask_rect : 'a1 -> (int -> 'a1) -> 'a1 -> mask -> 'a1
  
  val mask_rec : 'a1 -> (int -> 'a1) -> 'a1 -> mask -> 'a1
  
  val succ_double_mask : mask -> mask
  
  val double_mask : mask -> mask
  
  val double_pred_mask : int -> mask
  
  val pred_mask : mask -> mask
  
  val sub_mask : int -> int -> mask
  
  val sub_mask_carry : int -> int -> mask
  
  val sub : int -> int -> int
  
  val mul : int -> int -> int
  
  val iter : int -> ('a1 -> 'a1) -> 'a1 -> 'a1
  
  val pow : int -> int -> int
  
  val square : int -> int
  
  val div2 : int -> int
  
  val div2_up : int -> int
  
  val size_nat : int -> int
  
  val size : int -> int
  
  val compare_cont : int -> int -> comparison -> comparison
  
  val compare : int -> int -> comparison
  
  val min : int -> int -> int
  
  val max : int -> int -> int
  
  val eqb : int -> int -> bool
  
  val leb : int -> int -> bool
  
  val ltb : int -> int -> bool
  
  val sqrtrem_step :
    (int -> int) -> (int -> int) -> (int * mask) -> int * mask
  
  val sqrtrem : int -> int * mask
  
  val sqrt : int -> int
  
  val gcdn : int -> int -> int -> int
  
  val gcd : int -> int -> int
  
  val ggcdn : int -> int -> int -> int * (int * int)
  
  val ggcd : int -> int -> int * (int * int)
  
  val coq_Nsucc_double : int -> int
  
  val coq_Ndouble : int -> int
  
  val coq_lor : int -> int -> int
  
  val coq_land : int -> int -> int
  
  val ldiff : int -> int -> int
  
  val coq_lxor : int -> int -> int
  
  val shiftl_nat : int -> int -> int
  
  val shiftr_nat : int -> int -> int
  
  val shiftl : int -> int -> int
  
  val shiftr : int -> int -> int
  
  val testbit_nat : int -> int -> bool
  
  val testbit : int -> int -> bool
  
  val iter_op : ('a1 -> 'a1 -> 'a1) -> int -> 'a1 -> 'a1
  
  val to_nat : int -> int
  
  val of_nat : int -> int
  
  val of_succ_nat : int -> int
 end

module Coq_Pos : 
 sig 
  type t = int
  
  val succ : int -> int
  
  val add : int -> int -> int
  
  val add_carry : int -> int -> int
  
  val pred_double : int -> int
  
  val pred : int -> int
  
  val pred_N : int -> int
  
  type mask = Pos.mask =
  | IsNul
  | IsPos of int
  | IsNeg
  
  val mask_rect : 'a1 -> (int -> 'a1) -> 'a1 -> mask -> 'a1
  
  val mask_rec : 'a1 -> (int -> 'a1) -> 'a1 -> mask -> 'a1
  
  val succ_double_mask : mask -> mask
  
  val double_mask : mask -> mask
  
  val double_pred_mask : int -> mask
  
  val pred_mask : mask -> mask
  
  val sub_mask : int -> int -> mask
  
  val sub_mask_carry : int -> int -> mask
  
  val sub : int -> int -> int
  
  val mul : int -> int -> int
  
  val iter : int -> ('a1 -> 'a1) -> 'a1 -> 'a1
  
  val pow : int -> int -> int
  
  val square : int -> int
  
  val div2 : int -> int
  
  val div2_up : int -> int
  
  val size_nat : int -> int
  
  val size : int -> int
  
  val compare_cont : int -> int -> comparison -> comparison
  
  val compare : int -> int -> comparison
  
  val min : int -> int -> int
  
  val max : int -> int -> int
  
  val eqb : int -> int -> bool
  
  val leb : int -> int -> bool
  
  val ltb : int -> int -> bool
  
  val sqrtrem_step :
    (int -> int) -> (int -> int) -> (int * mask) -> int * mask
  
  val sqrtrem : int -> int * mask
  
  val sqrt : int -> int
  
  val gcdn : int -> int -> int -> int
  
  val gcd : int -> int -> int
  
  val ggcdn : int -> int -> int -> int * (int * int)
  
  val ggcd : int -> int -> int * (int * int)
  
  val coq_Nsucc_double : int -> int
  
  val coq_Ndouble : int -> int
  
  val coq_lor : int -> int -> int
  
  val coq_land : int -> int -> int
  
  val ldiff : int -> int -> int
  
  val coq_lxor : int -> int -> int
  
  val shiftl_nat : int -> int -> int
  
  val shiftr_nat : int -> int -> int
  
  val shiftl : int -> int -> int
  
  val shiftr : int -> int -> int
  
  val testbit_nat : int -> int -> bool
  
  val testbit : int -> int -> bool
  
  val iter_op : ('a1 -> 'a1 -> 'a1) -> int -> 'a1 -> 'a1
  
  val to_nat : int -> int
  
  val of_nat : int -> int
  
  val of_succ_nat : int -> int
  
  val eq_dec : int -> int -> bool
  
  val peano_rect : 'a1 -> (int -> 'a1 -> 'a1) -> int -> 'a1
  
  val peano_rec : 'a1 -> (int -> 'a1 -> 'a1) -> int -> 'a1
  
  type coq_PeanoView =
  | PeanoOne
  | PeanoSucc of int * coq_PeanoView
  
  val coq_PeanoView_rect :
    'a1 -> (int -> coq_PeanoView -> 'a1 -> 'a1) -> int -> coq_PeanoView ->
    'a1
  
  val coq_PeanoView_rec :
    'a1 -> (int -> coq_PeanoView -> 'a1 -> 'a1) -> int -> coq_PeanoView ->
    'a1
  
  val peanoView_xO : int -> coq_PeanoView -> coq_PeanoView
  
  val peanoView_xI : int -> coq_PeanoView -> coq_PeanoView
  
  val peanoView : int -> coq_PeanoView
  
  val coq_PeanoView_iter :
    'a1 -> (int -> 'a1 -> 'a1) -> int -> coq_PeanoView -> 'a1
  
  val eqb_spec : int -> int -> reflect
  
  val switch_Eq : comparison -> comparison -> comparison
  
  val mask2cmp : mask -> comparison
  
  val leb_spec0 : int -> int -> reflect
  
  val ltb_spec0 : int -> int -> reflect
  
  module Private_Tac : 
   sig 
    
   end
  
  module Private_Rev : 
   sig 
    module ORev : 
     sig 
      type t = int
     end
    
    module MRev : 
     sig 
      val max : int -> int -> int
     end
    
    module MPRev : 
     sig 
      module Private_Tac : 
       sig 
        
       end
     end
   end
  
  module Private_Dec : 
   sig 
    val max_case_strong :
      int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ ->
      'a1) -> 'a1
    
    val max_case :
      int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1
    
    val max_dec : int -> int -> bool
    
    val min_case_strong :
      int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ ->
      'a1) -> 'a1
    
    val min_case :
      int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1
    
    val min_dec : int -> int -> bool
   end
  
  val max_case_strong : int -> int -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
  
  val max_case : int -> int -> 'a1 -> 'a1 -> 'a1
  
  val max_dec : int -> int -> bool
  
  val min_case_strong : int -> int -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
  
  val min_case : int -> int -> 'a1 -> 'a1 -> 'a1
  
  val min_dec : int -> int -> bool
 end

module N : 
 sig 
  type t = int
  
  val zero : int
  
  val one : int
  
  val two : int
  
  val succ_double : int -> int
  
  val double : int -> int
  
  val succ : int -> int
  
  val pred : int -> int
  
  val succ_pos : int -> int
  
  val add : int -> int -> int
  
  val sub : int -> int -> int
  
  val mul : int -> int -> int
  
  val compare : int -> int -> comparison
  
  val eqb : int -> int -> bool
  
  val leb : int -> int -> bool
  
  val ltb : int -> int -> bool
  
  val min : int -> int -> int
  
  val max : int -> int -> int
  
  val div2 : int -> int
  
  val even : int -> bool
  
  val odd : int -> bool
  
  val pow : int -> int -> int
  
  val square : int -> int
  
  val log2 : int -> int
  
  val size : int -> int
  
  val size_nat : int -> int
  
  val pos_div_eucl : int -> int -> int * int
  
  val div_eucl : int -> int -> int * int
  
  val div : int -> int -> int
  
  val modulo : int -> int -> int
  
  val gcd : int -> int -> int
  
  val ggcd : int -> int -> int * (int * int)
  
  val sqrtrem : int -> int * int
  
  val sqrt : int -> int
  
  val coq_lor : int -> int -> int
  
  val coq_land : int -> int -> int
  
  val ldiff : int -> int -> int
  
  val coq_lxor : int -> int -> int
  
  val shiftl_nat : int -> int -> int
  
  val shiftr_nat : int -> int -> int
  
  val shiftl : int -> int -> int
  
  val shiftr : int -> int -> int
  
  val testbit_nat : int -> int -> bool
  
  val testbit : int -> int -> bool
  
  val to_nat : int -> int
  
  val of_nat : int -> int
  
  val iter : int -> ('a1 -> 'a1) -> 'a1 -> 'a1
  
  val eq_dec : int -> int -> bool
  
  val discr : int -> int option
  
  val binary_rect :
    'a1 -> (int -> 'a1 -> 'a1) -> (int -> 'a1 -> 'a1) -> int -> 'a1
  
  val binary_rec :
    'a1 -> (int -> 'a1 -> 'a1) -> (int -> 'a1 -> 'a1) -> int -> 'a1
  
  val peano_rect : 'a1 -> (int -> 'a1 -> 'a1) -> int -> 'a1
  
  val peano_rec : 'a1 -> (int -> 'a1 -> 'a1) -> int -> 'a1
  
  val leb_spec0 : int -> int -> reflect
  
  val ltb_spec0 : int -> int -> reflect
  
  module Private_BootStrap : 
   sig 
    
   end
  
  val recursion : 'a1 -> (int -> 'a1 -> 'a1) -> int -> 'a1
  
  module Private_OrderTac : 
   sig 
    module Elts : 
     sig 
      type t = int
     end
    
    module Tac : 
     sig 
      
     end
   end
  
  module Private_NZPow : 
   sig 
    
   end
  
  module Private_NZSqrt : 
   sig 
    
   end
  
  val sqrt_up : int -> int
  
  val log2_up : int -> int
  
  module Private_NZDiv : 
   sig 
    
   end
  
  val lcm : int -> int -> int
  
  val eqb_spec : int -> int -> reflect
  
  val b2n : bool -> int
  
  val setbit : int -> int -> int
  
  val clearbit : int -> int -> int
  
  val ones : int -> int
  
  val lnot : int -> int -> int
  
  module Private_Tac : 
   sig 
    
   end
  
  module Private_Rev : 
   sig 
    module ORev : 
     sig 
      type t = int
     end
    
    module MRev : 
     sig 
      val max : int -> int -> int
     end
    
    module MPRev : 
     sig 
      module Private_Tac : 
       sig 
        
       end
     end
   end
  
  module Private_Dec : 
   sig 
    val max_case_strong :
      int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ ->
      'a1) -> 'a1
    
    val max_case :
      int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1
    
    val max_dec : int -> int -> bool
    
    val min_case_strong :
      int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ ->
      'a1) -> 'a1
    
    val min_case :
      int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1
    
    val min_dec : int -> int -> bool
   end
  
  val max_case_strong : int -> int -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
  
  val max_case : int -> int -> 'a1 -> 'a1 -> 'a1
  
  val max_dec : int -> int -> bool
  
  val min_case_strong : int -> int -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
  
  val min_case : int -> int -> 'a1 -> 'a1 -> 'a1
  
  val min_dec : int -> int -> bool
 end

module Z : 
 sig 
  type t = int
  
  val zero : int
  
  val one : int
  
  val two : int
  
  val double : int -> int
  
  val succ_double : int -> int
  
  val pred_double : int -> int
  
  val pos_sub : int -> int -> int
  
  val add : int -> int -> int
  
  val opp : int -> int
  
  val succ : int -> int
  
  val pred : int -> int
  
  val sub : int -> int -> int
  
  val mul : int -> int -> int
  
  val pow_pos : int -> int -> int
  
  val pow : int -> int -> int
  
  val square : int -> int
  
  val compare : int -> int -> comparison
  
  val sgn : int -> int
  
  val leb : int -> int -> bool
  
  val ltb : int -> int -> bool
  
  val geb : int -> int -> bool
  
  val gtb : int -> int -> bool
  
  val eqb : int -> int -> bool
  
  val max : int -> int -> int
  
  val min : int -> int -> int
  
  val abs : int -> int
  
  val abs_nat : int -> int
  
  val abs_N : int -> int
  
  val to_nat : int -> int
  
  val to_N : int -> int
  
  val of_nat : int -> int
  
  val of_N : int -> int
  
  val to_pos : int -> int
  
  val iter : int -> ('a1 -> 'a1) -> 'a1 -> 'a1
  
  val pos_div_eucl : int -> int -> int * int
  
  val div_eucl : int -> int -> int * int
  
  val div : int -> int -> int
  
  val modulo : int -> int -> int
  
  val quotrem : int -> int -> int * int
  
  val quot : int -> int -> int
  
  val rem : int -> int -> int
  
  val even : int -> bool
  
  val odd : int -> bool
  
  val div2 : int -> int
  
  val quot2 : int -> int
  
  val log2 : int -> int
  
  val sqrtrem : int -> int * int
  
  val sqrt : int -> int
  
  val gcd : int -> int -> int
  
  val ggcd : int -> int -> int * (int * int)
  
  val testbit : int -> int -> bool
  
  val shiftl : int -> int -> int
  
  val shiftr : int -> int -> int
  
  val coq_lor : int -> int -> int
  
  val coq_land : int -> int -> int
  
  val ldiff : int -> int -> int
  
  val coq_lxor : int -> int -> int
  
  val eq_dec : int -> int -> bool
  
  module Private_BootStrap : 
   sig 
    
   end
  
  val leb_spec0 : int -> int -> reflect
  
  val ltb_spec0 : int -> int -> reflect
  
  module Private_OrderTac : 
   sig 
    module Elts : 
     sig 
      type t = int
     end
    
    module Tac : 
     sig 
      
     end
   end
  
  val sqrt_up : int -> int
  
  val log2_up : int -> int
  
  module Private_NZDiv : 
   sig 
    
   end
  
  module Private_Div : 
   sig 
    module Quot2Div : 
     sig 
      val div : int -> int -> int
      
      val modulo : int -> int -> int
     end
    
    module NZQuot : 
     sig 
      
     end
   end
  
  val lcm : int -> int -> int
  
  val eqb_spec : int -> int -> reflect
  
  val b2z : bool -> int
  
  val setbit : int -> int -> int
  
  val clearbit : int -> int -> int
  
  val lnot : int -> int
  
  val ones : int -> int
  
  module Private_Tac : 
   sig 
    
   end
  
  module Private_Rev : 
   sig 
    module ORev : 
     sig 
      type t = int
     end
    
    module MRev : 
     sig 
      val max : int -> int -> int
     end
    
    module MPRev : 
     sig 
      module Private_Tac : 
       sig 
        
       end
     end
   end
  
  module Private_Dec : 
   sig 
    val max_case_strong :
      int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ ->
      'a1) -> 'a1
    
    val max_case :
      int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1
    
    val max_dec : int -> int -> bool
    
    val min_case_strong :
      int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ ->
      'a1) -> 'a1
    
    val min_case :
      int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1
    
    val min_dec : int -> int -> bool
   end
  
  val max_case_strong : int -> int -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
  
  val max_case : int -> int -> 'a1 -> 'a1 -> 'a1
  
  val max_dec : int -> int -> bool
  
  val min_case_strong : int -> int -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
  
  val min_case : int -> int -> 'a1 -> 'a1 -> 'a1
  
  val min_dec : int -> int -> bool
 end

type 'a predb = 'a -> bool

val or0 : bool -> bool -> bool

val neg : bool -> bool

type decidable =
  bool
  (* singleton inductive, whose constructor was decidable_make *)

type 'a comparable =
  'a -> 'a -> decidable
  (* singleton inductive, whose constructor was make_comparable *)

val bool_comparable : bool comparable

val my_Z_of_nat : int -> int

val fold_right : ('a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 list -> 'a2

val fold_left : ('a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 list -> 'a2

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val filter : 'a1 predb -> 'a1 list -> 'a1 list

val append : 'a1 list -> 'a1 list -> 'a1 list

val rev : 'a1 list -> 'a1 list

val split : ('a1 * 'a2) list -> 'a1 list * 'a2 list

val append0 : char list -> char list -> char list

val string_comparable : char list comparable

val and_decidable : decidable -> decidable -> decidable

val in_decidable : 'a1 comparable -> 'a1 -> 'a1 list -> decidable

module type HeapSpec = 
 sig 
  type ('x0, 'x) heap 
  
  val empty : ('a1, 'a2) heap
  
  val write : ('a1, 'a2) heap -> 'a1 -> 'a2 -> ('a1, 'a2) heap
  
  val to_list : ('a1, 'a2) heap -> ('a1 * 'a2) list
  
  val read : 'a1 comparable -> ('a1, 'a2) heap -> 'a1 -> 'a2
  
  val read_option : 'a1 comparable -> ('a1, 'a2) heap -> 'a1 -> 'a2 option
  
  val rem : 'a1 comparable -> ('a1, 'a2) heap -> 'a1 -> ('a1, 'a2) heap
  
  val indom_decidable : 'a1 comparable -> ('a1, 'a2) heap -> 'a1 -> decidable
 end

module HeapList : 
 HeapSpec

type binary64 = float

type number = binary64

val number_of_int : int -> number

val number_add : number -> number -> number

val number_mult : number -> number -> number

val number_div : number -> number -> number

type binary_op =
| Binary_op_add
| Binary_op_mult
| Binary_op_div
| Binary_op_equal
| Binary_op_instanceof
| Binary_op_in

type unary_op =
| Unary_op_not
| Unary_op_delete
| Unary_op_typeof
| Unary_op_pre_incr
| Unary_op_post_incr
| Unary_op_pre_decr
| Unary_op_post_decr
| Unary_op_void

type literal =
| Literal_null
| Literal_bool of bool
| Literal_number of number
| Literal_string of char list

type expr =
| Expr_this
| Expr_variable of char list
| Expr_literal of literal
| Expr_object of (char list * expr) list
| Expr_function of char list option * char list list * expr
| Expr_access of expr * expr
| Expr_member of expr * char list
| Expr_new of expr * expr list
| Expr_call of expr * expr list
| Expr_unary_op of unary_op * expr
| Expr_binary_op of expr * binary_op * expr
| Expr_and of expr * expr
| Expr_or of expr * expr
| Expr_assign of expr * binary_op option * expr
| Expr_seq of expr * expr
| Expr_var_decl of char list * expr option
| Expr_if of expr * expr * expr option
| Expr_while of expr * expr
| Expr_with of expr * expr
| Expr_skip

type loc =
| Loc_normal of int
| Loc_null
| Loc_scope
| Loc_global
| Loc_eval
| Loc_obj_proto
| Loc_func_proto
| Loc_eval_proto

type field =
| Field_normal of char list
| Field_proto
| Field_body
| Field_scope
| Field_this

val field_normal_prototype : field

type ref =
| Ref of loc * field

type scope = loc list

type value =
| Value_undef
| Value_bool of bool
| Value_number of number
| Value_string of char list
| Value_loc of loc
| Value_scope of scope
| Value_body of char list list * expr

type result =
| Result_value of value
| Result_ref of ref

module Heap : 
 sig 
  type ('x0, 'x) heap = ('x0, 'x) HeapList.heap
  
  val empty : ('a1, 'a2) heap
  
  val write : ('a1, 'a2) heap -> 'a1 -> 'a2 -> ('a1, 'a2) heap
  
  val to_list : ('a1, 'a2) heap -> ('a1 * 'a2) list
  
  val read : 'a1 comparable -> ('a1, 'a2) heap -> 'a1 -> 'a2
  
  val read_option : 'a1 comparable -> ('a1, 'a2) heap -> 'a1 -> 'a2 option
  
  val rem : 'a1 comparable -> ('a1, 'a2) heap -> 'a1 -> ('a1, 'a2) heap
  
  val indom_decidable : 'a1 comparable -> ('a1, 'a2) heap -> 'a1 -> decidable
 end

type heap0 = (ref, value) Heap.heap

val loc_comparable : loc comparable

val ref_comparable : ref comparable

val number_comparable : number comparable

val value_compare : value -> value -> bool

val empty_heap : heap0

val write0 : heap0 -> loc -> field -> value -> (ref, value) Heap.heap

val write_fields : heap0 -> loc -> (field * value) list -> heap0

val write_proto : heap0 -> loc -> loc -> (ref, value) Heap.heap

val write_this : heap0 -> loc -> loc -> (ref, value) Heap.heap

val read0 : heap0 -> loc -> field -> value

val rem0 : heap0 -> loc -> field -> (ref, value) Heap.heap

val update : heap0 -> loc -> field -> value -> (ref, value) Heap.heap

val dealloc : heap0 -> result -> heap0

val init_heap : (ref, value) Heap.heap

val init_scope : loc list

val value_of_literal : literal -> value

val get_this : heap0 -> result -> loc

val alloc_obj : heap0 -> loc -> loc -> (ref, value) Heap.heap

val alloc_fun :
  heap0 -> loc -> scope -> char list list -> expr -> loc -> heap0

val reserve_local_vars : heap0 -> loc -> char list list -> heap0

val obj_of_value : value -> loc -> loc

val obj_or_glob_of_value : value -> loc

val defs : char list list -> expr -> char list list

val indom_decidable0 : heap0 -> loc -> field -> decidable

val fresh_for_list : (ref * value) list -> loc

val fresh_for : heap0 -> loc

val basic_value_decidable : value -> decidable

val proto_comp_body :
  (heap0 -> field -> loc -> loc) -> heap0 -> field -> loc -> loc

val proto_comp : heap0 -> field -> loc -> loc

val scope_comp : heap0 -> field -> scope -> loc

val getvalue_comp : heap0 -> result -> value option

val mnostuck : bool

type ret =
| Ret_result of result
| Ret_exn of result

type out =
| Out_return of heap0 * ret
| Out_unspec
| Out_bottom

val make_error :
  heap0
  ->
  char list
  ->
  out

val ret_ref :
  loc
  ->
  field
  ->
  ret

val wrong :
  heap0
  ->
  out

val if_success :
  out
  ->
  (heap0
  ->
  result
  ->
  out)
  ->
  out

val if_defined :
  heap0
  ->
  'a1
  option
  ->
  ('a1
  ->
  out)
  ->
  out

val if_success_value :
  out
  ->
  (heap0
  ->
  value
  ->
  out)
  ->
  out

val if_is_ref :
  heap0
  ->
  result
  ->
  (loc
  ->
  field
  ->
  out)
  ->
  out

val if_is_field_normal :
  heap0
  ->
  field
  ->
  (char list
  ->
  out)
  ->
  out

val if_eq :
  loc
  ->
  heap0
  ->
  value
  option
  ->
  (__
  ->
  out)
  ->
  (loc
  ->
  out)
  ->
  out

val if_not_eq :
  loc
  ->
  heap0
  ->
  value
  option
  ->
  (loc
  ->
  out)
  ->
  out

val if_is_null_ref :
  result
  ->
  (field
  ->
  out)
  ->
  (result
  ->
  out)
  ->
  out

val if_is_string :
  heap0
  ->
  value
  option
  ->
  (char list
  ->
  out)
  ->
  out

val if_binds_field :
  field
  ->
  heap0
  ->
  loc
  ->
  (value
  ->
  out)
  ->
  out

val if_binds_scope_body :
  heap0
  ->
  loc
  ->
  (scope
  ->
  char list
  list
  ->
  expr
  ->
  out)
  ->
  out

val if_binds_field_loc :
  field
  ->
  heap0
  ->
  loc
  ->
  (loc
  ->
  out)
  ->
  out

val if_boolean :
  heap0
  ->
  value
  ->
  (__
  ->
  out)
  ->
  (__
  ->
  out)
  ->
  out

val if_convert_to_bool :
  heap0
  ->
  value
  ->
  (__
  ->
  out)
  ->
  (__
  ->
  out)
  ->
  out

val dont_delete_comparable :
  result
  ->
  decidable

val if_is_loc_value :
  value
  ->
  (loc
  ->
  value
  option)
  ->
  value
  option

val binary_op_comp_body :
  (binary_op
  ->
  heap0
  ->
  value
  ->
  value
  ->
  value
  option)
  ->
  binary_op
  ->
  heap0
  ->
  value
  ->
  value
  ->
  value
  option

val binary_op_comp :
  binary_op
  ->
  heap0
  ->
  value
  ->
  value
  ->
  value
  option

val unary_op_comp :
  unary_op
  ->
  heap0
  ->
  value
  ->
  value
  option

val typeof_comp :
  heap0
  ->
  value
  ->
  char list
  option

val arguments_comp :
  char list
  list
  ->
  value
  list
  ->
  (field * value)
  list

val run :
  int
  ->
  heap0
  ->
  scope
  ->
  expr
  ->
  out

val run_list_value :
  int
  ->
  heap0
  ->
  scope
  ->
  value
  list
  ->
  expr
  list
  ->
  (heap0
  ->
  value
  list
  ->
  out)
  ->
  out

val expr_undef :
  expr

val seq :
  expr
  list
  ->
  expr

val max_int :
  int

val prog1 :
  expr

val computation1 :
  out

val expr_var_decl' :
  char list
  ->
  expr
  ->
  expr

val expr_assign' :
  expr
  ->
  expr
  ->
  expr

val prog2 :
  expr

val computation2 :
  out

val prog3 :
  expr

val computation3 :
  out

