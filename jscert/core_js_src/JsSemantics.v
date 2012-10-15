Set Implicit Arguments.
Require Export JsSyntax JsSyntaxAux.
Implicit Type e : expr.
Implicit Type g : string.
Implicit Type x : string.
Implicit Type m : number.
Implicit Type h : heap.
Implicit Type v : value.
Implicit Type l : loc.
Implicit Type f : field.


(**************************************************************)
(** ** Auxiliary definitions for the semantics *)

(*--------------------------------------------------------------*)
(** Binding relation and freshness *)

(** [binds h l f v] asserts that the reference [Ref l f] is bound
    to [v] in the heap [h] *)

Definition binds h l f v :=
  Heap.binds h (Ref l f) v.

(** [indom h l f] asserts that [Ref l f] is bound to some value
    in the heap [h] *)

Definition indom h l f :=
  Heap.indom h (Ref l f).

(** A location [l] is used in [h] if there exists at least one
    field [f] such that [Ref l f] is a key in [h]. *)

Definition bound h l :=
  exists f, indom h l f.

(** A location [l] is fresh for [h] if it is not null and if
   there is no key of the form [Ref l f] bound by [h] *)

Definition fresh h l :=
  l <> loc_null /\ ~ bound h l.

(** There always exist fresh locations *) 
(* TODO: prove based on the fact that a domain is a finite set *)

Parameter fresh_exists : forall h,
  exists l, fresh h l.

(*--------------------------------------------------------------*)
(** Low-level operations on heaps *)

Definition empty_heap : heap :=
  Heap.empty.

(** [write h l f v] extends a heap [h] by mapping [Ref l f] to [v],
    where [l] is a location and [f] a field name *)

Definition write h l f v := 
  Heap.write h (Ref l f) v.

(** [write_fields h l fvs] write_fields pairs of fields and values into
    the object at location l. *)

Definition write_fields h l fvs :=
  fold_left (fun fv acc => let '(f,v) := fv in write acc l f v) h fvs.

(** [write_proto h l l'] is a shorthand for writing the prototype
    field of a location. *)

Definition write_proto h l l' :=
  write h l field_proto (value_loc l').

(** [write_this h l l'] is a shorthand for writing the "this"
    field of a location. *)

Definition write_this h l l' :=
  write h l field_this (value_loc l').

(** [read h l f] returns the content of cell at key [Ref l f],
    and is unspecified otherwise *)

Definition read h l f :=
  Heap.read h (Ref l f).

(** [rem h l f] removes the binding on [Ref l f] from the heap [h] *)

Definition rem h l f :=
  Heap.rem h (Ref l f).


(*--------------------------------------------------------------*)
(** High-level javascript operations on heaps *)

(** [update h l f v] write_fields [v] at [(l,f)], except if [l] is null
    in which case it write_fields [v] at [(loc_global,f)] 
    (definition of "h[(l,x)->v]" from the paper) *)

Definition update h l f v :=
  let l' := ifb l = loc_null then loc_global else l
  in write h l' f v.

(** [dealloc h r] captures the deallocation policy.
    (definition of "h \ r" from the paper) *)

Definition dealloc h r :=
  match r with
  | result_value v => h
  | result_ref (Ref l f) => rem h l f
  end.


(**************************************************************)
(** ** Initial heap and scope *)

(** Definition of the initial heap *)

Definition init_heap := 
  let h0 := empty_heap in
  let h1 := write_proto h0 loc_global loc_obj_proto in
  let h2 := write_proto h1 loc_obj_proto loc_null in
  let h3 := write_proto h2 loc_func_proto loc_obj_proto in
  let h4 := write_proto h3 loc_scope loc_null in
  let h5 := write_this h4 loc_scope loc_global in
  h5.

(** Definition of the initial scope *)

Definition init_scope := 
  loc_global::loc_scope::nil.


(*--------------------------------------------------------------*)
(** Basic values and prototype and scope resolution *)

(** Basic values: values that are not closures nor 
    locations, except for the null location *)

Inductive basic_value : value -> Prop :=
  | basic_undef :
      basic_value value_undef
  | basic_bool : forall b,
      basic_value (value_bool b)
  | basic_number : forall m,
      basic_value (value_number m)
  | basic_string : forall g,
      basic_value (value_string g)
  | basic_null :
      basic_value (value_loc loc_null).

(** Prototype resolution (definition of "\pi" in the paper) *)

Inductive proto : heap -> field -> loc -> loc -> Prop :=
  | proto_null : forall h f,
      proto h f loc_null loc_null
  | proto_here : forall h l f,
      indom h l f ->
      proto h f l l
  | proto_next : forall h l f l' l'',
      ~ indom h l f ->
      binds h l field_proto l' ->
      proto h f l' l'' ->
      proto h f l l''.

(** Scope resolution (definition of "\sigma" in the paper) *)

Inductive scopes : heap -> field -> scope -> loc -> Prop :=
  | scopes_nil : forall h f,
      scopes h f nil loc_null 
  | scopes_here : forall h s f l l',
      proto h f l l' -> l' <> loc_null ->
      scopes h f (l::s) l
  | scopes_next : forall h s f l l',
      proto h f l loc_null ->
      scopes h f s l' ->
      scopes h f (l::s) l'.

(** Dereferencing values (definition of "\gamma" in the paper) *)

Inductive getvalue : heap -> result -> value -> Prop :=
  | getvalue_value : forall h v,
      getvalue h (result_value v) v
  | getvalue_ref_not_null : forall h l l' x v,
      proto h (field_normal x) l l' -> 
      l <> loc_null ->
      l' <> loc_null ->
      binds h l' (field_normal x) v ->
      getvalue h (Ref l (field_normal x)) v
  | getvalue_ref_null : forall h x l,
      proto h (field_normal x) l loc_null ->
      l <> loc_null ->
      getvalue h (Ref l (field_normal x)) value_undef.


(*--------------------------------------------------------------*)
(** Other auxiliary definitions *)

(** Translation from literal to values *) 

Definition value_of_literal i :=
  match i with
  | literal_null => value_loc loc_null
  | literal_bool b => value_bool b
  | literal_number m => value_number m 
  | literal_string g => value_string g
  end.

(** Getting the this object (definition of "This" from the paper) *)

Definition get_this h r :=
  match r with
  | result_value v => loc_global
  | result_ref (Ref l n) => 
      ifb indom h l field_this
        then loc_global 
        else l
  end.

(** Definition of ready-only (definitions of "RO" from the paper *)

Definition is_read_only h r :=
  match r with
  | result_value v => False
  | result_ref (Ref l f) => f = field_normal_prototype 
                      /\ indom h l field_body
  end.

(** Specification of fields that cannot be deallocated *)

Definition dont_delete r :=
  match r with
  | result_value v => False
  | result_ref (Ref l f) => 
       f = field_proto \/ f = field_this  
    \/ f = field_scope \/ f = field_normal_prototype
  end.

(** Macro for allocation a new object *)

Definition alloc_obj h l l' :=
  write_proto h l l'.

(** Macro r allocation a function *)

Definition alloc_fun h l' s lx e l :=
  write_fields h l' (
    (field_proto, value_loc loc_func_proto)::
    (field_normal_prototype, value_loc l)::
    (field_scope, value_scope s)::
    (field_body, value_body lx e)::
    nil).

(** Macro for allocating local variables *)

Definition reserve_local_vars h l ys :=
  write_fields h l (LibList.map (fun y => (field_normal y, value_undef)) ys).

(** Macro for extracting a location out of a value if possible,
    otherwise returning a given location *)

Definition obj_of_value v l :=
  match v with
  | value_loc l1 => ifb l1 = loc_null then l else l1
  | _ => l
  end.

(** Macro for extracting a location out of a value,
    otherwise returning the location of the global object *)

Definition obj_or_glob_of_value v :=
  obj_of_value v loc_obj_proto.  

(* LATER: use [[@call]] method in the semantic. *)

Definition indom_scope_or_body h l :=
  exists v, binds h l field_scope v \/ binds h l field_body v.


(** List of arguments for function calls:
    [arguments lx lv lxv] asserts that [lxv] is a list made of 
    the corresponding pairs of names and values in [lx] and [lv]. 
    If [lx] is shorter than [lv], excess values are droped from [lv].
    If [lv] is shorter than [lx], then [lv] is completed with [value_undef]. *)

Inductive arguments : list string -> list value -> list (field * value) -> Prop :=
  | arguments_nil_vars : forall lv, 
      arguments nil lv nil
  | arguments_nil_values : forall lx x lfm,
      arguments lx nil lfm ->
      arguments (x::lx) nil ((field_normal x, value_undef)::lfm)
  | arguments_cons : forall lx lv x v lfm,
      arguments lx lv lfm ->
      arguments (x::lx) (v::lv) ((field_normal x, v)::lfm).

(* ARTHUR: what is the behavior in case several arguments have the same name?
   do we have a shadowing behavior, or is the program rejected upfront? 
   If we have shadowing, it is happening in the right order? *)


(*--------------------------------------------------------------*)
(** Parsing relation for eval. LATER: implement *)

Parameter parse : string -> expr -> Prop.


(*--------------------------------------------------------------*)
(** Local variables *)

(** Computing local variables of an expression *)

Fixpoint defs (lx:list string) (e:expr) : (list string) :=
  let d := defs lx in
  match e with
  | expr_this => nil
  | expr_variable x => nil
  | expr_literal v => nil
  | expr_object lxe => nil
  | expr_function no lx e => nil
  | expr_access e1 e2 => nil
  | expr_member e y => nil
  | expr_new e1 le2 => nil
  | expr_call e1 le2 => nil
  | expr_unary_op op e => nil
  | expr_binary_op e1 op e2 => nil 
  | expr_and e1 e2 => nil
  | expr_or e1 e2 => nil
  | expr_assign e1 oop e2 => nil
  | expr_seq e1 e2 => d e1 ++ d e2
  | expr_var_decl y oe => ifb In y lx then nil else (y::nil)
  | expr_if e1 e2 None => d e2 
  | expr_if e1 e2 (Some e3) => d e2 ++ d e3
  | expr_while e1 e2 => d e2
  | expr_with e1 e2 => d e2
  | expr_skip => nil
  end.


(**************************************************************)
(** ** Reduction rules for operators *)

(** Semantics of [instanceof] *)

Inductive instanceof_red : heap -> loc -> value -> value -> Prop :=

  | instanceof_red_value : forall l v h,
      basic_value v ->
      instanceof_red h l v (value_bool false)

  | instanceof_red_true : forall l l1 l2 h,
      binds h l field_normal_prototype (value_loc l2) ->
      binds h l1 field_proto (value_loc l2) ->
      instanceof_red h l (value_loc l1) (value_bool true)

  | instanceof_red_trans : forall l l1 l2 l3 h v',
      binds h l1 field_proto (value_loc l3) ->
      binds h l field_normal_prototype (value_loc l2) ->
      l2 <> l3 ->
      instanceof_red h l (value_loc l3) v' ->
      instanceof_red h l (value_loc l1) v'.

      (*NEWSYNTAX: the above definition does not seem to give full coverage *) 

(** Binary operators *)

Inductive binary_op_red : binary_op -> heap -> value -> value -> value -> Prop :=

  | binary_op_red_add_number : forall h m m',
      binary_op_red binary_op_add h m m' (number_add m m')

  | binary_op_red_add_str : forall h g g',
      binary_op_red binary_op_add h (value_string g) (value_string g')
        (value_string (String.append g g'))

  | binary_op_red_mult_number : forall h m m',
      binary_op_red binary_op_mult h m m' (number_mult m m')

  | binary_op_red_div_number : forall h m m',
      binary_op_red binary_op_div h m m' (number_div m m')

  | binary_op_red_equal : forall h v v', 
      basic_value v -> 
      basic_value v' ->
      binary_op_red binary_op_equal h v v' (value_bool (isTrue (v=v')))

  | binary_op_red_in : forall h x l l' b,
      proto h (field_normal x) l l' ->
      b = (If l' = loc_null then false else true) ->
      binary_op_red binary_op_in h (value_string x) (value_loc l) (value_bool b)
      (* NEWSYNTAX: please check above refactorization *)

  | binary_op_red_instanceof : forall h l v v',
      instanceof_red h l v v' ->
      binary_op_red binary_op_instanceof h l v v'.

(** Unary operators *)

Inductive unary_op_red : unary_op -> heap -> value -> value -> Prop :=

  | unary_op_red_void : forall v h,
      unary_op_red unary_op_void h v (value_undef)

  | unary_op_red_not : forall b h,
      unary_op_red unary_op_not h (value_bool b) (value_bool (neg b)).

(** Operator typeof *)

Inductive typeof_red : heap -> value -> string -> Prop :=

  | typeof_red_undef : forall h, 
      typeof_red h value_undef "undefined"

  | typeof_red_null : forall h, 
      typeof_red h (value_loc loc_null) "object"

  | typeof_red_bool : forall h b, 
      typeof_red h (value_bool b) "boolean"

  | typeof_red_string : forall h x,
      typeof_red h (value_string x) "string"

  | typeof_red_number : forall h m, 
      typeof_red h (value_number m) "number"

  | typeof_red_function : forall h l,
      indom_scope_or_body h l ->
      typeof_red h (value_loc l) "function"

  | typeof_red_object : forall h l,
      ~ indom_scope_or_body h l ->
      typeof_red h (value_loc l) "object".


(**************************************************************)
(** ** Reduction rules for expressions *)

Inductive red : heap -> scope -> expr -> heap -> result -> Prop :=

  | red_this : forall h0 s l1 l2 l3,
      scopes h0 field_this s l1 ->
      proto h0 field_this l1 l2 ->
      binds h0 l2 field_this l3 ->
      red h0 s expr_this h0 l3

  | red_variable : forall h s x l, 
      scopes h x s l ->
      red h s (expr_variable x) h (Ref l x)
 
  | red_literal : forall h0 s i,
      red h0 s (expr_literal i) h0 (value_of_literal i)

  | red_object : forall h0 h1 h2 h3 s l lxe lx le lv lfv, 
      fresh h0 l ->
      h1 = alloc_obj h0 l loc_obj_proto ->
      (lx,le) = LibList.split lxe ->
      red_list_value h1 s le h2 lv ->
      (*NEWSYNTAX: can replace next line with 
        [let lfv := List.combine lx lv] or even better 
        [Forall3 (fun x v xv => xv = (x,v)) lx lv lfv] *)
      arguments lx lv lfv -> 
      h3 = write_fields h2 l lfv ->
      red h0 s (expr_object lxe) h3 l

  | red_function_unnamed : forall l l' h0 h1 h2 s lx e, 
      fresh h0 l -> 
      h1 = alloc_obj h0 l loc_obj_proto ->
      fresh h1 l' -> 
      h2 = alloc_fun h1 l' s lx e l ->
      red h0 s (expr_function None lx e) h2 l'

  | red_function_named : forall l l' l1 h0 h1 h2 h3 h4 s y lx e, 
      fresh h0 l -> 
      h1 = alloc_obj h0 l loc_obj_proto -> 
      fresh h1 l1 ->
      h2 = alloc_obj h1 l1 loc_obj_proto ->
      fresh h2 l' ->  
      h3 = alloc_fun h2 l' (l1::s) lx e l ->
      h4 = write h3 l1 (field_normal y) (value_loc l') ->
      red h0 s (expr_function (Some y) lx e) h4 l'

  | red_eval : forall h0 h1 h2 h3 s g e1 e2 e3 r1 r2 r3 v3,
      red h0 s e1 h1 r1 -> getvalue h1 r1 loc_eval ->
      red h1 s e2 h2 r2 -> getvalue h2 r2 (value_string g) ->
      parse g e3 ->
      red h2 s e3 h3 r3 -> getvalue h3 r3 v3 ->
      red h0 s (expr_call e1 (e2::nil)) h3 v3

  | red_access : forall l x h0 h1 h2 s e1 e2 r1 r2, 
     (* LATER: change the order when we introduce exceptions *)
      red h0 s e1 h1 r1 -> getvalue h1 r1 l -> l <> loc_null ->
      red h1 s e2 h2 r2 -> getvalue h2 r2 (value_string x) ->
      red h0 s (expr_access e1 e2) h2 (Ref l x)

  | red_member : forall l x h0 h2 s e1 r, 
      red h0 s (expr_access e1 (expr_literal (literal_string x))) h2 r ->
      red h0 s (expr_member e1 x) h2 r

  | red_new : forall l l1 l2 l3 l4 v1 lv2 s3 lx ys e3,
              forall h0 h1 h2 h3 h4 h5 h6 h7 h8 s e1 le2 r1 r3 v3 lfv,
      (* Evaluate constructor *)
      red h0 s e1 h1 r1 ->
      getvalue h1 r1 l1 ->
      l1 <> loc_null ->
      binds h1 l1 field_scope (value_scope s3) ->
      binds h1 l1 field_body (value_body lx e3) ->
      ys = defs lx e3 ->
      binds h1 l1 field_normal_prototype v1 ->
      l2 = obj_or_glob_of_value v1 ->
      (* Evaluate parameters *)
      red_list_value h1 s le2 h2 lv2 ->
      (* Init new object *)
      fresh h2 l4 ->
      h3 = alloc_obj h2 l4 l2 ->
      (* Create activation record *)
      fresh h3 l3 ->
      (* ys = defs lx e3 -> *)(* LATER *)
      h4 = write h3 l3 field_proto (value_loc loc_null) ->
      h5 = write h4 l3 field_this (value_loc l4) ->
      arguments lx lv2 lfv ->
      h6 = write_fields h5 l3 lfv ->
      h7 = reserve_local_vars h6 l3 ys ->
      (* Execute function (constructor) body *)
      red h7 (l3::s3) e3 h8 r3 ->
      getvalue h8 r3 v3 ->
      l = obj_of_value v3 l4 ->
      red h0 s (expr_new e1 le2) h8 l

  | red_call : forall l1 l2 l3 lv2 s3 lx ys e3,
               forall h0 h1 h2 h3 h4 h5 h6 h7 s e1 le2 r1 r3 v3 lfv,
      red h0 s e1 h1 r1 -> getvalue h1 r1 l1 ->
      l2 = get_this h1 r1 ->
      l1 <> loc_eval -> 
      binds h1 l1 field_scope (value_scope s3) ->
      binds h1 l1 field_body (value_body lx e3) ->
      ys = defs lx e3 ->
      red_list_value h1 s le2 h2 lv2 ->
      fresh h2 l3 -> 
      h3 = alloc_obj h2 l3 loc_null ->
      h4 = write h3 l3 field_this l2 ->
      arguments lx lv2 lfv ->
      h5 = write_fields h4 l3 lfv ->
      h6 = reserve_local_vars h5 l3 ys ->
      red h6 (l3::s3) e3 h7 r3 -> getvalue h7 r3 v3 ->
      red h0 s (expr_call e1 le2) h7 v3

  | red_unary_op : forall h0 h1 s e r1 v1 op v,
      red h0 s e h1 r1 -> getvalue h1 r1 v1 ->
      unary_op_red op h1 v1 v ->
      red h0 s (expr_unary_op op e) h1 v

  | red_typeof_value : forall h0 h1 s e r1 v1 str,
      red h0 s e h1 r1 -> getvalue h1 r1 v1 ->
      typeof_red h1 v1 str ->
      red h0 s (expr_unary_op unary_op_typeof e) h1 (value_string str)

  | red_typeof_undefined : forall h0 h1 s e f,
      red h0 s e h1 (Ref loc_null f) ->
      red h0 s (expr_unary_op unary_op_typeof e) h1 (value_string "undefined")

  | red_pre_incr : forall h0 h1 h2 s e l x v va,
      red h0 s e h1 (Ref l x) -> getvalue h1 (Ref l x) v ->
      binary_op_red binary_op_add h0 (number_of_int 1) v va ->
      h2 = update h1 l x va ->
      red h0 s (expr_unary_op unary_op_pre_incr e) h2 v

  | red_pre_decr : forall h0 h1 h2 s e l x v va,
      red h0 s e h1 (Ref l x) -> getvalue h1 (Ref l x) v ->
      binary_op_red binary_op_add h0 (number_of_int (-1)%Z) v va ->
      h2 = update h1 l x va ->
      red h0 s (expr_unary_op unary_op_pre_decr e) h2 v

  | red_post_incr : forall h0 h1 h2 s e l x v va,
      red h0 s e h1 (Ref l x) -> getvalue h1 (Ref l x) v ->
      binary_op_red binary_op_add h0 (number_of_int 1) v va ->
      h2 = update h1 l x va ->
      red h0 s (expr_unary_op unary_op_post_incr e) h2 va

  | red_post_decr : forall h0 h1 h2 s e l x v va,
      red h0 s e h1 (Ref l x) -> getvalue h1 (Ref l x) v ->
      binary_op_red binary_op_add h0 (number_of_int (-1)%Z) v va ->
      h2 = update h1 l x va ->
      red h0 s (expr_unary_op unary_op_post_decr e) h2 va

  | red_delete_true : forall h0 h1 h2 s e r,
      red h0 s e h1 r ->
      ~ dont_delete r ->
      h2 = dealloc h1 r ->
      red h0 s (expr_unary_op unary_op_delete e) h2 (value_bool true)
      (* LATER: will raise an exception if r is loc_null *)

  | red_delete_false : forall h0 h1 s e r,
      red h0 s e h1 r ->
      dont_delete r ->
      red h0 s (expr_unary_op unary_op_delete e) h1 (value_bool false)

  | red_binary_op : forall h0 h1 h2 s e1 e2 r1 r2 v1 v2 op v,
      red h0 s e1 h1 r1 -> getvalue h1 r1 v1 ->
      red h1 s e2 h2 r2 -> getvalue h2 r2 v2 ->
      binary_op_red op h2 v1 v2 v ->
      red h0 s (expr_binary_op e1 op e2) h2 v

  | red_and_true : forall h0 h1 h2 s e1 e2 r1 r2 v1 v2,
      red h0 s e1 h1 r1 -> getvalue h1 r1 v1 ->
      v1 = value_bool true -> (* Later: Type conversion here. *)
      red h1 s e2 h2 r2 -> getvalue h2 r2 v2 ->
      red h0 s (expr_and e1 e2) h2 v2

  | red_and_false : forall h0 h1 s e1 e2 r1 v1,
      red h0 s e1 h1 r1 -> getvalue h1 r1 v1 ->
      v1 = value_bool false -> (* Later: Type conversion here. *)
      red h0 s (expr_and e1 e2) h1 v1

  | red_or_true : forall h0 h1 s e1 e2 r1 v1,
      red h0 s e1 h1 r1 -> getvalue h1 r1 v1 ->
      v1 = value_bool true -> (* Later: Type conversion here. *)
      red h0 s (expr_or e1 e2) h1 v1

  | red_or_false : forall h0 h1 h2 s e1 e2 r1 r2 v1 v2,
      red h0 s e1 h1 r1 -> getvalue h1 r1 v1 ->
      v1 = value_bool false -> (* Later: Type conversion here. *)
      red h1 s e2 h2 r2 -> getvalue h2 r2 v2 ->
      red h0 s (expr_or e1 e2) h2 v2

  | red_assign : forall l x v h0 h1 h2 h3 s e1 e2 r2, 
      red h0 s e1 h1 (Ref l x) ->
      red h1 s e2 h2 r2 -> 
      getvalue h2 r2 v ->
      h3 = update h2 l x v ->
      red h0 s (expr_assign e1 None e2) h3 v

  | red_assign_op : forall l x op v v1 v2 h0 h1 h2 h3 s e1 e2 r2,
      red h0 s e1 h1 (Ref l x) -> getvalue h1 (Ref l x) v1 ->
      (* LATER: change the order when we introduce exceptions *)
      (* ARTHUR: can't we do it now? *)
      (* NEWSYNTAX: old definition was broken with introduction of literal
      red h1 s (expr_binary_op (expr_literal v1) op e2) h2 r2 -> getvalue h2 r2 v ->
      *)
      red h1 s e2 h2 r2 -> getvalue h2 r2 v2 ->
      binary_op_red op h2 v1 v2 v ->
      h3 = update h2 l x v ->
      red h0 s (expr_assign e1 (Some op) e2) h3 v

  | red_seq : forall h0 h1 h2 s e1 e2 r1 r2,
      red h0 s e1 h1 r1 -> 
      red h1 s e2 h2 r2 ->
      red h0 s (expr_seq e1 e2) h2 r2

  | red_var_decl : forall h0 s x,
      red h0 s (expr_var_decl x None) h0 value_undef

  | red_var_decl_expr : forall h0 h1 s x e r1,
      red h0 s (expr_assign (expr_variable x) None e) h1 r1 ->
      red h0 s (expr_var_decl x (Some e)) h1 value_undef

  | red_if_true : forall h0 h1 h2 s e1 e2 o3 r1 r2,
      red h0 s e1 h1 r1 -> getvalue h1 r1 (value_bool true) -> 
      red h1 s e2 h2 r2 ->
      red h0 s (expr_if e1 e2 o3) h2 r2

  | red_if_false : forall h0 h1 h2 s e1 e2 e3 r1 r2,
      red h0 s e1 h1 r1 -> getvalue h1 r1 (value_bool false) -> 
      red h1 s e3 h2 r2 ->
      red h0 s (expr_if e1 e2 (Some e3)) h2 r2

  | red_if_false_implicit : forall h0 h1 s e1 e2 r1,
      red h0 s e1 h1 r1 -> getvalue h1 r1 (value_bool false) -> 
      red h0 s (expr_if e1 e2 None) h1 value_undef
      (* NEWSYNTAX: check the above definition *)

  | red_while_true : forall h0 h1 h2 s e1 e2 r1 r2,
      red h0 s e1 h1 r1 -> getvalue h1 r1 (value_bool true) -> 
      red h1 s (expr_while e1 e2) h2 r2 ->
      red h0 s (expr_while e1 e2) h2 value_undef

  | red_while_false : forall h0 h1 s e1 e2 r1,
      red h0 s e1 h1 r1 -> getvalue h1 r1 (value_bool false) -> 
      red h0 s (expr_while e1 e2) h1 value_undef

  | red_with : forall l h0 h1 h2 s e1 e2 r1 r2,
      red h0 s e1 h1 r1 -> getvalue h1 r1 l -> 
      l <> loc_null ->
      red h1 (l::s) e2 h2 r2 ->
      red h0 s (expr_with e1 e2) h2 r2
      (* LATER: if l is not an object, then fault *)

  | red_skip : forall h0 s,
      red h0 s expr_skip h0 value_undef


with red_list_value : heap -> scope -> list expr -> heap -> list value -> Prop :=
  
  | red_list_nil : forall h s,
      red_list_value h s nil h nil

  | red_list_cons : forall h1 h2 h3 s e r v le lv,
      red h1 s e h2 r -> getvalue h2 r v ->
      red_list_value h2 s le h3 lv ->
      red_list_value h1 s (e::le) h3 (v::lv).


