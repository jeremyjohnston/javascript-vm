type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, y) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (x, y) -> y

type comparison =
| Eq
| Lt
| Gt

type compareSpecT =
| CompEqT
| CompLtT
| CompGtT

(** val compareSpec2Type : comparison -> compareSpecT **)

let compareSpec2Type = function
| Eq -> CompEqT
| Lt -> CompLtT
| Gt -> CompGtT

type 'a compSpecT = compareSpecT

(** val compSpec2Type : 'a1 -> 'a1 -> comparison -> 'a1 compSpecT **)

let compSpec2Type x y c =
  compareSpec2Type c

type 'a sig0 =
  'a
  (* singleton inductive, whose constructor was exist *)

(** val plus : int -> int -> int **)

let rec plus = (+)

(** val nat_iter : int -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

let rec nat_iter n f x =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    x)
    (fun n' ->
    f (nat_iter n' f x))
    n

type reflect =
| ReflectT
| ReflectF

(** val iff_reflect : bool -> reflect **)

let iff_reflect = function
| true -> ReflectT
| false -> ReflectF

module type TotalOrder' = 
 sig 
  type t 
 end

module MakeOrderTac = 
 functor (O:TotalOrder') ->
 struct 
  
 end

module MaxLogicalProperties = 
 functor (O:TotalOrder') ->
 functor (M:sig 
  val max : O.t -> O.t -> O.t
 end) ->
 struct 
  module Private_Tac = MakeOrderTac(O)
 end

module Pos = 
 struct 
  type t = int
  
  (** val succ : int -> int **)
  
  let rec succ x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> (fun p->2*p)
      (succ p))
      (fun p -> (fun p->1+2*p)
      p)
      (fun _ -> (fun p->2*p)
      1)
      x
  
  (** val add : int -> int -> int **)
  
  let rec add x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->2*p)
        (add_carry p q))
        (fun q -> (fun p->1+2*p)
        (add p q))
        (fun _ -> (fun p->2*p)
        (succ p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p)
        (add p q))
        (fun q -> (fun p->2*p)
        (add p q))
        (fun _ -> (fun p->1+2*p)
        p)
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->2*p)
        (succ q))
        (fun q -> (fun p->1+2*p)
        q)
        (fun _ -> (fun p->2*p)
        1)
        y)
      x
  
  (** val add_carry : int -> int -> int **)
  
  and add_carry x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p)
        (add_carry p q))
        (fun q -> (fun p->2*p)
        (add_carry p q))
        (fun _ -> (fun p->1+2*p)
        (succ p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->2*p)
        (add_carry p q))
        (fun q -> (fun p->1+2*p)
        (add p q))
        (fun _ -> (fun p->2*p)
        (succ p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p)
        (succ q))
        (fun q -> (fun p->2*p)
        (succ q))
        (fun _ -> (fun p->1+2*p)
        1)
        y)
      x
  
  (** val pred_double : int -> int **)
  
  let rec pred_double x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> (fun p->1+2*p) ((fun p->2*p)
      p))
      (fun p -> (fun p->1+2*p)
      (pred_double p))
      (fun _ ->
      1)
      x
  
  (** val pred : int -> int **)
  
  let pred x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> (fun p->2*p)
      p)
      (fun p ->
      pred_double p)
      (fun _ ->
      1)
      x
  
  (** val pred_N : int -> int **)
  
  let pred_N x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> ((fun p->2*p)
      p))
      (fun p ->
      (pred_double p))
      (fun _ ->
      0)
      x
  
  type mask =
  | IsNul
  | IsPos of int
  | IsNeg
  
  (** val mask_rect : 'a1 -> (int -> 'a1) -> 'a1 -> mask -> 'a1 **)
  
  let mask_rect f f0 f1 = function
  | IsNul -> f
  | IsPos x -> f0 x
  | IsNeg -> f1
  
  (** val mask_rec : 'a1 -> (int -> 'a1) -> 'a1 -> mask -> 'a1 **)
  
  let mask_rec f f0 f1 = function
  | IsNul -> f
  | IsPos x -> f0 x
  | IsNeg -> f1
  
  (** val succ_double_mask : mask -> mask **)
  
  let succ_double_mask = function
  | IsNul -> IsPos 1
  | IsPos p -> IsPos ((fun p->1+2*p) p)
  | IsNeg -> IsNeg
  
  (** val double_mask : mask -> mask **)
  
  let double_mask = function
  | IsPos p -> IsPos ((fun p->2*p) p)
  | x0 -> x0
  
  (** val double_pred_mask : int -> mask **)
  
  let double_pred_mask x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> IsPos ((fun p->2*p) ((fun p->2*p)
      p)))
      (fun p -> IsPos ((fun p->2*p)
      (pred_double p)))
      (fun _ ->
      IsNul)
      x
  
  (** val pred_mask : mask -> mask **)
  
  let pred_mask = function
  | IsPos q ->
    ((fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
       (fun p0 -> IsPos
       (pred q))
       (fun p0 -> IsPos
       (pred q))
       (fun _ ->
       IsNul)
       q)
  | _ -> IsNeg
  
  (** val sub_mask : int -> int -> mask **)
  
  let rec sub_mask x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q ->
        double_mask (sub_mask p q))
        (fun q ->
        succ_double_mask (sub_mask p q))
        (fun _ -> IsPos ((fun p->2*p)
        p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q ->
        succ_double_mask (sub_mask_carry p q))
        (fun q ->
        double_mask (sub_mask p q))
        (fun _ -> IsPos
        (pred_double p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p ->
        IsNeg)
        (fun p ->
        IsNeg)
        (fun _ ->
        IsNul)
        y)
      x
  
  (** val sub_mask_carry : int -> int -> mask **)
  
  and sub_mask_carry x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q ->
        succ_double_mask (sub_mask_carry p q))
        (fun q ->
        double_mask (sub_mask p q))
        (fun _ -> IsPos
        (pred_double p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q ->
        double_mask (sub_mask_carry p q))
        (fun q ->
        succ_double_mask (sub_mask_carry p q))
        (fun _ ->
        double_pred_mask p)
        y)
      (fun _ ->
      IsNeg)
      x
  
  (** val sub : int -> int -> int **)
  
  let sub x y =
    match sub_mask x y with
    | IsPos z -> z
    | _ -> 1
  
  (** val mul : int -> int -> int **)
  
  let rec mul x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      add y ((fun p->2*p) (mul p y)))
      (fun p -> (fun p->2*p)
      (mul p y))
      (fun _ ->
      y)
      x
  
  (** val iter : int -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)
  
  let rec iter n f x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun n' ->
      f (iter n' f (iter n' f x)))
      (fun n' ->
      iter n' f (iter n' f x))
      (fun _ ->
      f x)
      n
  
  (** val pow : int -> int -> int **)
  
  let pow x y =
    iter y (mul x) 1
  
  (** val square : int -> int **)
  
  let rec square p =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> (fun p->1+2*p) ((fun p->2*p)
      (add (square p0) p0)))
      (fun p0 -> (fun p->2*p) ((fun p->2*p)
      (square p0)))
      (fun _ ->
      1)
      p
  
  (** val div2 : int -> int **)
  
  let div2 p =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      p0)
      (fun p0 ->
      p0)
      (fun _ ->
      1)
      p
  
  (** val div2_up : int -> int **)
  
  let div2_up p =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      succ p0)
      (fun p0 ->
      p0)
      (fun _ ->
      1)
      p
  
  (** val size_nat : int -> int **)
  
  let rec size_nat p =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> succ
      (size_nat p0))
      (fun p0 -> succ
      (size_nat p0))
      (fun _ -> succ
      0)
      p
  
  (** val size : int -> int **)
  
  let rec size p =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      succ (size p0))
      (fun p0 ->
      succ (size p0))
      (fun _ ->
      1)
      p
  
  (** val compare_cont : int -> int -> comparison -> comparison **)
  
  let rec compare_cont x y r =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q ->
        compare_cont p q r)
        (fun q ->
        compare_cont p q Gt)
        (fun _ ->
        Gt)
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q ->
        compare_cont p q Lt)
        (fun q ->
        compare_cont p q r)
        (fun _ ->
        Gt)
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q ->
        Lt)
        (fun q ->
        Lt)
        (fun _ ->
        r)
        y)
      x
  
  (** val compare : int -> int -> comparison **)
  
  let compare x y =
    compare_cont x y Eq
  
  (** val min : int -> int -> int **)
  
  let min p p' =
    match compare p p' with
    | Gt -> p'
    | _ -> p
  
  (** val max : int -> int -> int **)
  
  let max p p' =
    match compare p p' with
    | Gt -> p
    | _ -> p'
  
  (** val eqb : int -> int -> bool **)
  
  let rec eqb p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 ->
        eqb p0 q0)
        (fun p1 ->
        false)
        (fun _ ->
        false)
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p1 ->
        false)
        (fun q0 ->
        eqb p0 q0)
        (fun _ ->
        false)
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p0 ->
        false)
        (fun p0 ->
        false)
        (fun _ ->
        true)
        q)
      p
  
  (** val leb : int -> int -> bool **)
  
  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true
  
  (** val ltb : int -> int -> bool **)
  
  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false
  
  (** val sqrtrem_step :
      (int -> int) -> (int -> int) -> (int * mask) -> int * mask **)
  
  let sqrtrem_step f g = function
  | (s, y) ->
    (match y with
     | IsPos r ->
       let s' = (fun p->1+2*p) ((fun p->2*p) s) in
       let r' = g (f r) in
       if leb s' r'
       then (((fun p->1+2*p) s), (sub_mask r' s'))
       else (((fun p->2*p) s), (IsPos r'))
     | _ ->
       (((fun p->2*p) s),
         (sub_mask (g (f 1)) ((fun p->2*p) ((fun p->2*p) 1)))))
  
  (** val sqrtrem : int -> int * mask **)
  
  let rec sqrtrem p =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p1 ->
        sqrtrem_step (fun x -> (fun p->1+2*p) x) (fun x -> (fun p->1+2*p) x)
          (sqrtrem p1))
        (fun p1 ->
        sqrtrem_step (fun x -> (fun p->2*p) x) (fun x -> (fun p->1+2*p) x)
          (sqrtrem p1))
        (fun _ -> (1, (IsPos ((fun p->2*p)
        1))))
        p0)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p1 ->
        sqrtrem_step (fun x -> (fun p->1+2*p) x) (fun x -> (fun p->2*p) x)
          (sqrtrem p1))
        (fun p1 ->
        sqrtrem_step (fun x -> (fun p->2*p) x) (fun x -> (fun p->2*p) x)
          (sqrtrem p1))
        (fun _ -> (1, (IsPos
        1)))
        p0)
      (fun _ -> (1,
      IsNul))
      p
  
  (** val sqrt : int -> int **)
  
  let sqrt p =
    fst (sqrtrem p)
  
  (** val gcdn : int -> int -> int -> int **)
  
  let rec gcdn n a b =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      1)
      (fun n0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun a' ->
        (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
          (fun b' ->
          match compare a' b' with
          | Eq -> a
          | Lt -> gcdn n0 (sub b' a') a
          | Gt -> gcdn n0 (sub a' b') b)
          (fun b0 ->
          gcdn n0 a b0)
          (fun _ ->
          1)
          b)
        (fun a0 ->
        (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
          (fun p ->
          gcdn n0 a0 b)
          (fun b0 -> (fun p->2*p)
          (gcdn n0 a0 b0))
          (fun _ ->
          1)
          b)
        (fun _ ->
        1)
        a)
      n
  
  (** val gcd : int -> int -> int **)
  
  let gcd a b =
    gcdn (plus (size_nat a) (size_nat b)) a b
  
  (** val ggcdn : int -> int -> int -> int * (int * int) **)
  
  let rec ggcdn n a b =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> (1, (a,
      b)))
      (fun n0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun a' ->
        (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
          (fun b' ->
          match compare a' b' with
          | Eq -> (a, (1, 1))
          | Lt ->
            let (g, p) = ggcdn n0 (sub b' a') a in
            let (ba, aa) = p in (g, (aa, (add aa ((fun p->2*p) ba))))
          | Gt ->
            let (g, p) = ggcdn n0 (sub a' b') b in
            let (ab, bb) = p in (g, ((add bb ((fun p->2*p) ab)), bb)))
          (fun b0 ->
          let (g, p) = ggcdn n0 a b0 in
          let (aa, bb) = p in (g, (aa, ((fun p->2*p) bb))))
          (fun _ -> (1, (a,
          1)))
          b)
        (fun a0 ->
        (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
          (fun p ->
          let (g, p0) = ggcdn n0 a0 b in
          let (aa, bb) = p0 in (g, (((fun p->2*p) aa), bb)))
          (fun b0 ->
          let (g, p) = ggcdn n0 a0 b0 in (((fun p->2*p) g), p))
          (fun _ -> (1, (a,
          1)))
          b)
        (fun _ -> (1, (1,
        b)))
        a)
      n
  
  (** val ggcd : int -> int -> int * (int * int) **)
  
  let ggcd a b =
    ggcdn (plus (size_nat a) (size_nat b)) a b
  
  (** val coq_Nsucc_double : int -> int **)
  
  let coq_Nsucc_double x =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ ->
      1)
      (fun p -> ((fun p->1+2*p)
      p))
      x
  
  (** val coq_Ndouble : int -> int **)
  
  let coq_Ndouble n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ ->
      0)
      (fun p -> ((fun p->2*p)
      p))
      n
  
  (** val coq_lor : int -> int -> int **)
  
  let rec coq_lor p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> (fun p->1+2*p)
        (coq_lor p0 q0))
        (fun q0 -> (fun p->1+2*p)
        (coq_lor p0 q0))
        (fun _ ->
        p)
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> (fun p->1+2*p)
        (coq_lor p0 q0))
        (fun q0 -> (fun p->2*p)
        (coq_lor p0 q0))
        (fun _ -> (fun p->1+2*p)
        p0)
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p0 ->
        q)
        (fun q0 -> (fun p->1+2*p)
        q0)
        (fun _ ->
        q)
        q)
      p
  
  (** val coq_land : int -> int -> int **)
  
  let rec coq_land p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 ->
        coq_Nsucc_double (coq_land p0 q0))
        (fun q0 ->
        coq_Ndouble (coq_land p0 q0))
        (fun _ ->
        1)
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 ->
        coq_Ndouble (coq_land p0 q0))
        (fun q0 ->
        coq_Ndouble (coq_land p0 q0))
        (fun _ ->
        0)
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p0 ->
        1)
        (fun q0 ->
        0)
        (fun _ ->
        1)
        q)
      p
  
  (** val ldiff : int -> int -> int **)
  
  let rec ldiff p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 ->
        coq_Ndouble (ldiff p0 q0))
        (fun q0 ->
        coq_Nsucc_double (ldiff p0 q0))
        (fun _ -> ((fun p->2*p)
        p0))
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 ->
        coq_Ndouble (ldiff p0 q0))
        (fun q0 ->
        coq_Ndouble (ldiff p0 q0))
        (fun _ ->
        p)
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p0 ->
        0)
        (fun q0 ->
        1)
        (fun _ ->
        0)
        q)
      p
  
  (** val coq_lxor : int -> int -> int **)
  
  let rec coq_lxor p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 ->
        coq_Ndouble (coq_lxor p0 q0))
        (fun q0 ->
        coq_Nsucc_double (coq_lxor p0 q0))
        (fun _ -> ((fun p->2*p)
        p0))
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 ->
        coq_Nsucc_double (coq_lxor p0 q0))
        (fun q0 ->
        coq_Ndouble (coq_lxor p0 q0))
        (fun _ -> ((fun p->1+2*p)
        p0))
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> ((fun p->2*p)
        q0))
        (fun q0 -> ((fun p->1+2*p)
        q0))
        (fun _ ->
        0)
        q)
      p
  
  (** val shiftl_nat : int -> int -> int **)
  
  let shiftl_nat p n =
    nat_iter n (fun x -> (fun p->2*p) x) p
  
  (** val shiftr_nat : int -> int -> int **)
  
  let shiftr_nat p n =
    nat_iter n div2 p
  
  (** val shiftl : int -> int -> int **)
  
  let shiftl p n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ ->
      p)
      (fun n0 ->
      iter n0 (fun x -> (fun p->2*p) x) p)
      n
  
  (** val shiftr : int -> int -> int **)
  
  let shiftr p n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ ->
      p)
      (fun n0 ->
      iter n0 div2 p)
      n
  
  (** val testbit_nat : int -> int -> bool **)
  
  let rec testbit_nat p n =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        true)
        (fun n' ->
        testbit_nat p0 n')
        n)
      (fun p0 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        false)
        (fun n' ->
        testbit_nat p0 n')
        n)
      (fun _ ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        true)
        (fun n0 ->
        false)
        n)
      p
  
  (** val testbit : int -> int -> bool **)
  
  let rec testbit p n =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ ->
        true)
        (fun n0 ->
        testbit p0 (pred_N n0))
        n)
      (fun p0 ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ ->
        false)
        (fun n0 ->
        testbit p0 (pred_N n0))
        n)
      (fun _ ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ ->
        true)
        (fun p0 ->
        false)
        n)
      p
  
  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> int -> 'a1 -> 'a1 **)
  
  let rec iter_op op p a =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      op a (iter_op op p0 (op a a)))
      (fun p0 ->
      iter_op op p0 (op a a))
      (fun _ ->
      a)
      p
  
  (** val to_nat : int -> int **)
  
  let to_nat x =
    iter_op plus x (succ 0)
  
  (** val of_nat : int -> int **)
  
  let rec of_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      1)
      (fun x ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        1)
        (fun n0 ->
        succ (of_nat x))
        x)
      n
  
  (** val of_succ_nat : int -> int **)
  
  let rec of_succ_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      1)
      (fun x ->
      succ (of_succ_nat x))
      n
 end

module Coq_Pos = 
 struct 
  type t = int
  
  (** val succ : int -> int **)
  
  let rec succ = succ
  
  (** val add : int -> int -> int **)
  
  let rec add = (+)
  
  (** val add_carry : int -> int -> int **)
  
  and add_carry x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p)
        (add_carry p q))
        (fun q -> (fun p->2*p)
        (add_carry p q))
        (fun _ -> (fun p->1+2*p)
        (succ p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->2*p)
        (add_carry p q))
        (fun q -> (fun p->1+2*p)
        (add p q))
        (fun _ -> (fun p->2*p)
        (succ p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p)
        (succ q))
        (fun q -> (fun p->2*p)
        (succ q))
        (fun _ -> (fun p->1+2*p)
        1)
        y)
      x
  
  (** val pred_double : int -> int **)
  
  let rec pred_double x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> (fun p->1+2*p) ((fun p->2*p)
      p))
      (fun p -> (fun p->1+2*p)
      (pred_double p))
      (fun _ ->
      1)
      x
  
  (** val pred : int -> int **)
  
  let pred = fun n -> max 1 (n-1)
  
  (** val pred_N : int -> int **)
  
  let pred_N x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> ((fun p->2*p)
      p))
      (fun p ->
      (pred_double p))
      (fun _ ->
      0)
      x
  
  type mask = Pos.mask =
  | IsNul
  | IsPos of int
  | IsNeg
  
  (** val mask_rect : 'a1 -> (int -> 'a1) -> 'a1 -> mask -> 'a1 **)
  
  let mask_rect f f0 f1 = function
  | IsNul -> f
  | IsPos x -> f0 x
  | IsNeg -> f1
  
  (** val mask_rec : 'a1 -> (int -> 'a1) -> 'a1 -> mask -> 'a1 **)
  
  let mask_rec f f0 f1 = function
  | IsNul -> f
  | IsPos x -> f0 x
  | IsNeg -> f1
  
  (** val succ_double_mask : mask -> mask **)
  
  let succ_double_mask = function
  | IsNul -> IsPos 1
  | IsPos p -> IsPos ((fun p->1+2*p) p)
  | IsNeg -> IsNeg
  
  (** val double_mask : mask -> mask **)
  
  let double_mask = function
  | IsPos p -> IsPos ((fun p->2*p) p)
  | x0 -> x0
  
  (** val double_pred_mask : int -> mask **)
  
  let double_pred_mask x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> IsPos ((fun p->2*p) ((fun p->2*p)
      p)))
      (fun p -> IsPos ((fun p->2*p)
      (pred_double p)))
      (fun _ ->
      IsNul)
      x
  
  (** val pred_mask : mask -> mask **)
  
  let pred_mask = function
  | IsPos q ->
    ((fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
       (fun p0 -> IsPos
       (pred q))
       (fun p0 -> IsPos
       (pred q))
       (fun _ ->
       IsNul)
       q)
  | _ -> IsNeg
  
  (** val sub_mask : int -> int -> mask **)
  
  let rec sub_mask x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q ->
        double_mask (sub_mask p q))
        (fun q ->
        succ_double_mask (sub_mask p q))
        (fun _ -> IsPos ((fun p->2*p)
        p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q ->
        succ_double_mask (sub_mask_carry p q))
        (fun q ->
        double_mask (sub_mask p q))
        (fun _ -> IsPos
        (pred_double p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p ->
        IsNeg)
        (fun p ->
        IsNeg)
        (fun _ ->
        IsNul)
        y)
      x
  
  (** val sub_mask_carry : int -> int -> mask **)
  
  and sub_mask_carry x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q ->
        succ_double_mask (sub_mask_carry p q))
        (fun q ->
        double_mask (sub_mask p q))
        (fun _ -> IsPos
        (pred_double p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q ->
        double_mask (sub_mask_carry p q))
        (fun q ->
        succ_double_mask (sub_mask_carry p q))
        (fun _ ->
        double_pred_mask p)
        y)
      (fun _ ->
      IsNeg)
      x
  
  (** val sub : int -> int -> int **)
  
  let sub = fun n m -> max 1 (n-m)
  
  (** val mul : int -> int -> int **)
  
  let rec mul = ( * )
  
  (** val iter : int -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)
  
  let rec iter n f x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun n' ->
      f (iter n' f (iter n' f x)))
      (fun n' ->
      iter n' f (iter n' f x))
      (fun _ ->
      f x)
      n
  
  (** val pow : int -> int -> int **)
  
  let pow x y =
    iter y (mul x) 1
  
  (** val square : int -> int **)
  
  let rec square p =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> (fun p->1+2*p) ((fun p->2*p)
      (add (square p0) p0)))
      (fun p0 -> (fun p->2*p) ((fun p->2*p)
      (square p0)))
      (fun _ ->
      1)
      p
  
  (** val div2 : int -> int **)
  
  let div2 p =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      p0)
      (fun p0 ->
      p0)
      (fun _ ->
      1)
      p
  
  (** val div2_up : int -> int **)
  
  let div2_up p =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      succ p0)
      (fun p0 ->
      p0)
      (fun _ ->
      1)
      p
  
  (** val size_nat : int -> int **)
  
  let rec size_nat p =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> succ
      (size_nat p0))
      (fun p0 -> succ
      (size_nat p0))
      (fun _ -> succ
      0)
      p
  
  (** val size : int -> int **)
  
  let rec size p =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      succ (size p0))
      (fun p0 ->
      succ (size p0))
      (fun _ ->
      1)
      p
  
  (** val compare_cont : int -> int -> comparison -> comparison **)
  
  let rec compare_cont = fun x y c -> if x=y then c else if x<y then Lt else Gt
  
  (** val compare : int -> int -> comparison **)
  
  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt
  
  (** val min : int -> int -> int **)
  
  let min = min
  
  (** val max : int -> int -> int **)
  
  let max = max
  
  (** val eqb : int -> int -> bool **)
  
  let rec eqb p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 ->
        eqb p0 q0)
        (fun p1 ->
        false)
        (fun _ ->
        false)
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p1 ->
        false)
        (fun q0 ->
        eqb p0 q0)
        (fun _ ->
        false)
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p0 ->
        false)
        (fun p0 ->
        false)
        (fun _ ->
        true)
        q)
      p
  
  (** val leb : int -> int -> bool **)
  
  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true
  
  (** val ltb : int -> int -> bool **)
  
  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false
  
  (** val sqrtrem_step :
      (int -> int) -> (int -> int) -> (int * mask) -> int * mask **)
  
  let sqrtrem_step f g = function
  | (s, y) ->
    (match y with
     | IsPos r ->
       let s' = (fun p->1+2*p) ((fun p->2*p) s) in
       let r' = g (f r) in
       if leb s' r'
       then (((fun p->1+2*p) s), (sub_mask r' s'))
       else (((fun p->2*p) s), (IsPos r'))
     | _ ->
       (((fun p->2*p) s),
         (sub_mask (g (f 1)) ((fun p->2*p) ((fun p->2*p) 1)))))
  
  (** val sqrtrem : int -> int * mask **)
  
  let rec sqrtrem p =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p1 ->
        sqrtrem_step (fun x -> (fun p->1+2*p) x) (fun x -> (fun p->1+2*p) x)
          (sqrtrem p1))
        (fun p1 ->
        sqrtrem_step (fun x -> (fun p->2*p) x) (fun x -> (fun p->1+2*p) x)
          (sqrtrem p1))
        (fun _ -> (1, (IsPos ((fun p->2*p)
        1))))
        p0)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p1 ->
        sqrtrem_step (fun x -> (fun p->1+2*p) x) (fun x -> (fun p->2*p) x)
          (sqrtrem p1))
        (fun p1 ->
        sqrtrem_step (fun x -> (fun p->2*p) x) (fun x -> (fun p->2*p) x)
          (sqrtrem p1))
        (fun _ -> (1, (IsPos
        1)))
        p0)
      (fun _ -> (1,
      IsNul))
      p
  
  (** val sqrt : int -> int **)
  
  let sqrt p =
    fst (sqrtrem p)
  
  (** val gcdn : int -> int -> int -> int **)
  
  let rec gcdn n a b =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      1)
      (fun n0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun a' ->
        (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
          (fun b' ->
          match compare a' b' with
          | Eq -> a
          | Lt -> gcdn n0 (sub b' a') a
          | Gt -> gcdn n0 (sub a' b') b)
          (fun b0 ->
          gcdn n0 a b0)
          (fun _ ->
          1)
          b)
        (fun a0 ->
        (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
          (fun p ->
          gcdn n0 a0 b)
          (fun b0 -> (fun p->2*p)
          (gcdn n0 a0 b0))
          (fun _ ->
          1)
          b)
        (fun _ ->
        1)
        a)
      n
  
  (** val gcd : int -> int -> int **)
  
  let gcd a b =
    gcdn (plus (size_nat a) (size_nat b)) a b
  
  (** val ggcdn : int -> int -> int -> int * (int * int) **)
  
  let rec ggcdn n a b =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> (1, (a,
      b)))
      (fun n0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun a' ->
        (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
          (fun b' ->
          match compare a' b' with
          | Eq -> (a, (1, 1))
          | Lt ->
            let (g, p) = ggcdn n0 (sub b' a') a in
            let (ba, aa) = p in (g, (aa, (add aa ((fun p->2*p) ba))))
          | Gt ->
            let (g, p) = ggcdn n0 (sub a' b') b in
            let (ab, bb) = p in (g, ((add bb ((fun p->2*p) ab)), bb)))
          (fun b0 ->
          let (g, p) = ggcdn n0 a b0 in
          let (aa, bb) = p in (g, (aa, ((fun p->2*p) bb))))
          (fun _ -> (1, (a,
          1)))
          b)
        (fun a0 ->
        (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
          (fun p ->
          let (g, p0) = ggcdn n0 a0 b in
          let (aa, bb) = p0 in (g, (((fun p->2*p) aa), bb)))
          (fun b0 ->
          let (g, p) = ggcdn n0 a0 b0 in (((fun p->2*p) g), p))
          (fun _ -> (1, (a,
          1)))
          b)
        (fun _ -> (1, (1,
        b)))
        a)
      n
  
  (** val ggcd : int -> int -> int * (int * int) **)
  
  let ggcd a b =
    ggcdn (plus (size_nat a) (size_nat b)) a b
  
  (** val coq_Nsucc_double : int -> int **)
  
  let coq_Nsucc_double x =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ ->
      1)
      (fun p -> ((fun p->1+2*p)
      p))
      x
  
  (** val coq_Ndouble : int -> int **)
  
  let coq_Ndouble n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ ->
      0)
      (fun p -> ((fun p->2*p)
      p))
      n
  
  (** val coq_lor : int -> int -> int **)
  
  let rec coq_lor p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> (fun p->1+2*p)
        (coq_lor p0 q0))
        (fun q0 -> (fun p->1+2*p)
        (coq_lor p0 q0))
        (fun _ ->
        p)
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> (fun p->1+2*p)
        (coq_lor p0 q0))
        (fun q0 -> (fun p->2*p)
        (coq_lor p0 q0))
        (fun _ -> (fun p->1+2*p)
        p0)
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p0 ->
        q)
        (fun q0 -> (fun p->1+2*p)
        q0)
        (fun _ ->
        q)
        q)
      p
  
  (** val coq_land : int -> int -> int **)
  
  let rec coq_land p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 ->
        coq_Nsucc_double
          (coq_land
            p0
            q0))
        (fun q0 ->
        coq_Ndouble
          (coq_land
            p0
            q0))
        (fun _ ->
        1)
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 ->
        coq_Ndouble
          (coq_land
            p0
            q0))
        (fun q0 ->
        coq_Ndouble
          (coq_land
            p0
            q0))
        (fun _ ->
        0)
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p0 ->
        1)
        (fun q0 ->
        0)
        (fun _ ->
        1)
        q)
      p
  
  (** val ldiff :
      int
      ->
      int
      ->
      int **)
  
  let rec ldiff p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 ->
        coq_Ndouble
          (ldiff
            p0
            q0))
        (fun q0 ->
        coq_Nsucc_double
          (ldiff
            p0
            q0))
        (fun _ ->
        ((fun p->2*p)
        p0))
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 ->
        coq_Ndouble
          (ldiff
            p0
            q0))
        (fun q0 ->
        coq_Ndouble
          (ldiff
            p0
            q0))
        (fun _ ->
        p)
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p0 ->
        0)
        (fun q0 ->
        1)
        (fun _ ->
        0)
        q)
      p
  
  (** val coq_lxor :
      int
      ->
      int
      ->
      int **)
  
  let rec coq_lxor p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 ->
        coq_Ndouble
          (coq_lxor
            p0
            q0))
        (fun q0 ->
        coq_Nsucc_double
          (coq_lxor
            p0
            q0))
        (fun _ ->
        ((fun p->2*p)
        p0))
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 ->
        coq_Nsucc_double
          (coq_lxor
            p0
            q0))
        (fun q0 ->
        coq_Ndouble
          (coq_lxor
            p0
            q0))
        (fun _ ->
        ((fun p->1+2*p)
        p0))
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 ->
        ((fun p->2*p)
        q0))
        (fun q0 ->
        ((fun p->1+2*p)
        q0))
        (fun _ ->
        0)
        q)
      p
  
  (** val shiftl_nat :
      int
      ->
      int
      ->
      int **)
  
  let shiftl_nat p n =
    nat_iter
      n
      (fun x ->
      (fun p->2*p)
      x)
      p
  
  (** val shiftr_nat :
      int
      ->
      int
      ->
      int **)
  
  let shiftr_nat p n =
    nat_iter
      n
      div2
      p
  
  (** val shiftl :
      int
      ->
      int
      ->
      int **)
  
  let shiftl p n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ ->
      p)
      (fun n0 ->
      iter
        n0
        (fun x ->
        (fun p->2*p)
        x)
        p)
      n
  
  (** val shiftr :
      int
      ->
      int
      ->
      int **)
  
  let shiftr p n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ ->
      p)
      (fun n0 ->
      iter
        n0
        div2
        p)
      n
  
  (** val testbit_nat :
      int
      ->
      int
      ->
      bool **)
  
  let rec testbit_nat p n =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        true)
        (fun n' ->
        testbit_nat
          p0
          n')
        n)
      (fun p0 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        false)
        (fun n' ->
        testbit_nat
          p0
          n')
        n)
      (fun _ ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        true)
        (fun n0 ->
        false)
        n)
      p
  
  (** val testbit :
      int
      ->
      int
      ->
      bool **)
  
  let rec testbit p n =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ ->
        true)
        (fun n0 ->
        testbit
          p0
          (pred_N
            n0))
        n)
      (fun p0 ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ ->
        false)
        (fun n0 ->
        testbit
          p0
          (pred_N
            n0))
        n)
      (fun _ ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ ->
        true)
        (fun p0 ->
        false)
        n)
      p
  
  (** val iter_op :
      ('a1
      ->
      'a1
      ->
      'a1)
      ->
      int
      ->
      'a1
      ->
      'a1 **)
  
  let rec iter_op op p a =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      op
        a
        (iter_op
          op
          p0
          (op
            a
            a)))
      (fun p0 ->
      iter_op
        op
        p0
        (op
          a
          a))
      (fun _ ->
      a)
      p
  
  (** val to_nat :
      int
      ->
      int **)
  
  let to_nat x =
    iter_op
      plus
      x
      (succ
      0)
  
  (** val of_nat :
      int
      ->
      int **)
  
  let rec of_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      1)
      (fun x ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        1)
        (fun n0 ->
        succ
          (of_nat
            x))
        x)
      n
  
  (** val of_succ_nat :
      int
      ->
      int **)
  
  let rec of_succ_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      1)
      (fun x ->
      succ
        (of_succ_nat
          x))
      n
  
  (** val eq_dec :
      int
      ->
      int
      ->
      bool **)
  
  let rec eq_dec p y0 =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p1 ->
        eq_dec
          p0
          p1)
        (fun p1 ->
        false)
        (fun _ ->
        false)
        y0)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p1 ->
        false)
        (fun p1 ->
        eq_dec
          p0
          p1)
        (fun _ ->
        false)
        y0)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p0 ->
        false)
        (fun p0 ->
        false)
        (fun _ ->
        true)
        y0)
      p
  
  (** val peano_rect :
      'a1
      ->
      (int
      ->
      'a1
      ->
      'a1)
      ->
      int
      ->
      'a1 **)
  
  let rec peano_rect a f p =
    let f2 =
      peano_rect
        (f
          1
          a)
        (fun p0 x ->
        f
          (succ
            ((fun p->2*p)
            p0))
          (f
            ((fun p->2*p)
            p0)
            x))
    in
    ((fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
       (fun q ->
       f
         ((fun p->2*p)
         q)
         (f2
           q))
       (fun q ->
       f2
         q)
       (fun _ ->
       a)
       p)
  
  (** val peano_rec :
      'a1
      ->
      (int
      ->
      'a1
      ->
      'a1)
      ->
      int
      ->
      'a1 **)
  
  let peano_rec =
    peano_rect
  
  type coq_PeanoView =
  | PeanoOne
  | PeanoSucc of int
     * coq_PeanoView
  
  (** val coq_PeanoView_rect :
      'a1
      ->
      (int
      ->
      coq_PeanoView
      ->
      'a1
      ->
      'a1)
      ->
      int
      ->
      coq_PeanoView
      ->
      'a1 **)
  
  let rec coq_PeanoView_rect f f0 p = function
  | PeanoOne ->
    f
  | PeanoSucc (p1,
               p2) ->
    f0
      p1
      p2
      (coq_PeanoView_rect
        f
        f0
        p1
        p2)
  
  (** val coq_PeanoView_rec :
      'a1
      ->
      (int
      ->
      coq_PeanoView
      ->
      'a1
      ->
      'a1)
      ->
      int
      ->
      coq_PeanoView
      ->
      'a1 **)
  
  let rec coq_PeanoView_rec f f0 p = function
  | PeanoOne ->
    f
  | PeanoSucc (p1,
               p2) ->
    f0
      p1
      p2
      (coq_PeanoView_rec
        f
        f0
        p1
        p2)
  
  (** val peanoView_xO :
      int
      ->
      coq_PeanoView
      ->
      coq_PeanoView **)
  
  let rec peanoView_xO p = function
  | PeanoOne ->
    PeanoSucc
      (1,
      PeanoOne)
  | PeanoSucc (p0,
               q0) ->
    PeanoSucc
      ((succ
         ((fun p->2*p)
         p0)),
      (PeanoSucc
      (((fun p->2*p)
      p0),
      (peanoView_xO
        p0
        q0))))
  
  (** val peanoView_xI :
      int
      ->
      coq_PeanoView
      ->
      coq_PeanoView **)
  
  let rec peanoView_xI p = function
  | PeanoOne ->
    PeanoSucc
      ((succ
         1),
      (PeanoSucc
      (1,
      PeanoOne)))
  | PeanoSucc (p0,
               q0) ->
    PeanoSucc
      ((succ
         ((fun p->1+2*p)
         p0)),
      (PeanoSucc
      (((fun p->1+2*p)
      p0),
      (peanoView_xI
        p0
        q0))))
  
  (** val peanoView :
      int
      ->
      coq_PeanoView **)
  
  let rec peanoView p =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      peanoView_xI
        p0
        (peanoView
          p0))
      (fun p0 ->
      peanoView_xO
        p0
        (peanoView
          p0))
      (fun _ ->
      PeanoOne)
      p
  
  (** val coq_PeanoView_iter :
      'a1
      ->
      (int
      ->
      'a1
      ->
      'a1)
      ->
      int
      ->
      coq_PeanoView
      ->
      'a1 **)
  
  let rec coq_PeanoView_iter a f p = function
  | PeanoOne ->
    a
  | PeanoSucc (p0,
               q0) ->
    f
      p0
      (coq_PeanoView_iter
        a
        f
        p0
        q0)
  
  (** val eqb_spec :
      int
      ->
      int
      ->
      reflect **)
  
  let eqb_spec x y =
    iff_reflect
      (eqb
        x
        y)
  
  (** val switch_Eq :
      comparison
      ->
      comparison
      ->
      comparison **)
  
  let switch_Eq c = function
  | Eq ->
    c
  | x ->
    x
  
  (** val mask2cmp :
      mask
      ->
      comparison **)
  
  let mask2cmp = function
  | IsNul ->
    Eq
  | IsPos p0 ->
    Gt
  | IsNeg ->
    Lt
  
  (** val leb_spec0 :
      int
      ->
      int
      ->
      reflect **)
  
  let leb_spec0 x y =
    iff_reflect
      (leb
        x
        y)
  
  (** val ltb_spec0 :
      int
      ->
      int
      ->
      reflect **)
  
  let ltb_spec0 x y =
    iff_reflect
      (ltb
        x
        y)
  
  module Private_Tac = 
   struct 
    
   end
  
  module Private_Rev = 
   struct 
    module ORev = 
     struct 
      type t
        =
        int
     end
    
    module MRev = 
     struct 
      (** val max :
          int
          ->
          int
          ->
          int **)
      
      let max x y =
        min
          y
          x
     end
    
    module MPRev = MaxLogicalProperties(ORev)(MRev)
   end
  
  module Private_Dec = 
   struct 
    (** val max_case_strong :
        int
        ->
        int
        ->
        (int
        ->
        int
        ->
        __
        ->
        'a1
        ->
        'a1)
        ->
        (__
        ->
        'a1)
        ->
        (__
        ->
        'a1)
        ->
        'a1 **)
    
    let max_case_strong n m compat hl hr =
      let c =
        compSpec2Type
          n
          m
          (compare
            n
            m)
      in
      (match c with
       | CompGtT ->
         compat
           n
           (max
             n
             m)
           __
           (hl
             __)
       | _ ->
         compat
           m
           (max
             n
             m)
           __
           (hr
             __))
    
    (** val max_case :
        int
        ->
        int
        ->
        (int
        ->
        int
        ->
        __
        ->
        'a1
        ->
        'a1)
        ->
        'a1
        ->
        'a1
        ->
        'a1 **)
    
    let max_case n m x x0 x1 =
      max_case_strong
        n
        m
        x
        (fun _ ->
        x0)
        (fun _ ->
        x1)
    
    (** val max_dec :
        int
        ->
        int
        ->
        bool **)
    
    let max_dec n m =
      max_case
        n
        m
        (fun x y _ h0 ->
        h0)
        true
        false
    
    (** val min_case_strong :
        int
        ->
        int
        ->
        (int
        ->
        int
        ->
        __
        ->
        'a1
        ->
        'a1)
        ->
        (__
        ->
        'a1)
        ->
        (__
        ->
        'a1)
        ->
        'a1 **)
    
    let min_case_strong n m compat hl hr =
      let c =
        compSpec2Type
          n
          m
          (compare
            n
            m)
      in
      (match c with
       | CompGtT ->
         compat
           m
           (min
             n
             m)
           __
           (hr
             __)
       | _ ->
         compat
           n
           (min
             n
             m)
           __
           (hl
             __))
    
    (** val min_case :
        int
        ->
        int
        ->
        (int
        ->
        int
        ->
        __
        ->
        'a1
        ->
        'a1)
        ->
        'a1
        ->
        'a1
        ->
        'a1 **)
    
    let min_case n m x x0 x1 =
      min_case_strong
        n
        m
        x
        (fun _ ->
        x0)
        (fun _ ->
        x1)
    
    (** val min_dec :
        int
        ->
        int
        ->
        bool **)
    
    let min_dec n m =
      min_case
        n
        m
        (fun x y _ h0 ->
        h0)
        true
        false
   end
  
  (** val max_case_strong :
      int
      ->
      int
      ->
      (__
      ->
      'a1)
      ->
      (__
      ->
      'a1)
      ->
      'a1 **)
  
  let max_case_strong n m x x0 =
    Private_Dec.max_case_strong
      n
      m
      (fun x1 y _ x2 ->
      x2)
      x
      x0
  
  (** val max_case :
      int
      ->
      int
      ->
      'a1
      ->
      'a1
      ->
      'a1 **)
  
  let max_case n m x x0 =
    max_case_strong
      n
      m
      (fun _ ->
      x)
      (fun _ ->
      x0)
  
  (** val max_dec :
      int
      ->
      int
      ->
      bool **)
  
  let max_dec =
    Private_Dec.max_dec
  
  (** val min_case_strong :
      int
      ->
      int
      ->
      (__
      ->
      'a1)
      ->
      (__
      ->
      'a1)
      ->
      'a1 **)
  
  let min_case_strong n m x x0 =
    Private_Dec.min_case_strong
      n
      m
      (fun x1 y _ x2 ->
      x2)
      x
      x0
  
  (** val min_case :
      int
      ->
      int
      ->
      'a1
      ->
      'a1
      ->
      'a1 **)
  
  let min_case n m x x0 =
    min_case_strong
      n
      m
      (fun _ ->
      x)
      (fun _ ->
      x0)
  
  (** val min_dec :
      int
      ->
      int
      ->
      bool **)
  
  let min_dec =
    Private_Dec.min_dec
 end

module N = 
 struct 
  type t
    =
    int
  
  (** val zero :
      int **)
  
  let zero =
    0
  
  (** val one :
      int **)
  
  let one =
    1
  
  (** val two :
      int **)
  
  let two =
    ((fun p->2*p)
      1)
  
  (** val succ_double :
      int
      ->
      int **)
  
  let succ_double x =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ ->
      1)
      (fun p ->
      ((fun p->1+2*p)
      p))
      x
  
  (** val double :
      int
      ->
      int **)
  
  let double n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ ->
      0)
      (fun p ->
      ((fun p->2*p)
      p))
      n
  
  (** val succ :
      int
      ->
      int **)
  
  let succ = succ
  
  (** val pred :
      int
      ->
      int **)
  
  let pred = fun n -> max 0 (n-1)
  
  (** val succ_pos :
      int
      ->
      int **)
  
  let succ_pos n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ ->
      1)
      (fun p ->
      Coq_Pos.succ
        p)
      n
  
  (** val add :
      int
      ->
      int
      ->
      int **)
  
  let add = (+)
  
  (** val sub :
      int
      ->
      int
      ->
      int **)
  
  let sub = fun n m -> max 0 (n-m)
  
  (** val mul :
      int
      ->
      int
      ->
      int **)
  
  let mul = ( * )
  
  (** val compare :
      int
      ->
      int
      ->
      comparison **)
  
  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt
  
  (** val eqb :
      int
      ->
      int
      ->
      bool **)
  
  let rec eqb n m =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ ->
        true)
        (fun p ->
        false)
        m)
      (fun p ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ ->
        false)
        (fun q ->
        Coq_Pos.eqb
          p
          q)
        m)
      n
  
  (** val leb :
      int
      ->
      int
      ->
      bool **)
  
  let leb x y =
    match compare
            x
            y with
    | Gt ->
      false
    | _ ->
      true
  
  (** val ltb :
      int
      ->
      int
      ->
      bool **)
  
  let ltb x y =
    match compare
            x
            y with
    | Lt ->
      true
    | _ ->
      false
  
  (** val min :
      int
      ->
      int
      ->
      int **)
  
  let min = min
  
  (** val max :
      int
      ->
      int
      ->
      int **)
  
  let max = max
  
  (** val div2 :
      int
      ->
      int **)
  
  let div2 n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ ->
      0)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p ->
        p)
        (fun p ->
        p)
        (fun _ ->
        0)
        p0)
      n
  
  (** val even :
      int
      ->
      bool **)
  
  let even n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ ->
      true)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p0 ->
        false)
        (fun p0 ->
        true)
        (fun _ ->
        false)
        p)
      n
  
  (** val odd :
      int
      ->
      bool **)
  
  let odd n =
    negb
      (even
        n)
  
  (** val pow :
      int
      ->
      int
      ->
      int **)
  
  let pow n p =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ ->
      1)
      (fun p0 ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ ->
        0)
        (fun q ->
        (Coq_Pos.pow
          q
          p0))
        n)
      p
  
  (** val square :
      int
      ->
      int **)
  
  let square n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ ->
      0)
      (fun p ->
      (Coq_Pos.square
        p))
      n
  
  (** val log2 :
      int
      ->
      int **)
  
  let log2 n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ ->
      0)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p ->
        (Coq_Pos.size
          p))
        (fun p ->
        (Coq_Pos.size
          p))
        (fun _ ->
        0)
        p0)
      n
  
  (** val size :
      int
      ->
      int **)
  
  let size n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ ->
      0)
      (fun p ->
      (Coq_Pos.size
        p))
      n
  
  (** val size_nat :
      int
      ->
      int **)
  
  let size_nat n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ ->
      0)
      (fun p ->
      Coq_Pos.size_nat
        p)
      n
  
  (** val pos_div_eucl :
      int
      ->
      int
      ->
      int * int **)
  
  let rec pos_div_eucl a b =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun a' ->
      let (q,
           r) =
        pos_div_eucl
          a'
          b
      in
      let r' =
        succ_double
          r
      in
      if leb
           b
           r'
      then ((succ_double
              q),
             (sub
               r'
               b))
      else ((double
              q),
             r'))
      (fun a' ->
      let (q,
           r) =
        pos_div_eucl
          a'
          b
      in
      let r' =
        double
          r
      in
      if leb
           b
           r'
      then ((succ_double
              q),
             (sub
               r'
               b))
      else ((double
              q),
             r'))
      (fun _ ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ ->
        (0,
        1))
        (fun p ->
        (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
          (fun p0 ->
          (0,
          1))
          (fun p0 ->
          (0,
          1))
          (fun _ ->
          (1,
          0))
          p)
        b)
      a
  
  (** val div_eucl :
      int
      ->
      int
      ->
      int * int **)
  
  let div_eucl a b =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ ->
      (0,
      0))
      (fun na ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ ->
        (0,
        a))
        (fun p ->
        pos_div_eucl
          na
          b)
        b)
      a
  
  (** val div :
      int
      ->
      int
      ->
      int **)
  
  let div = fun a b -> if b=0 then 0 else a/b
  
  (** val modulo :
      int
      ->
      int
      ->
      int **)
  
  let modulo = fun a b -> if b=0 then a else a mod b
  
  (** val gcd :
      int
      ->
      int
      ->
      int **)
  
  let gcd a b =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ ->
      b)
      (fun p ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ ->
        a)
        (fun q ->
        (Coq_Pos.gcd
          p
          q))
        b)
      a
  
  (** val ggcd :
      int
      ->
      int
      ->
      int * (int * int) **)
  
  let ggcd a b =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ ->
      (b,
      (0,
      1)))
      (fun p ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ ->
        (a,
        (1,
        0)))
        (fun q ->
        let (g,
             p0) =
          Coq_Pos.ggcd
            p
            q
        in
        let (aa,
             bb) =
          p0
        in
        (g,
        (aa,
        bb)))
        b)
      a
  
  (** val sqrtrem :
      int
      ->
      int * int **)
  
  let sqrtrem n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ ->
      (0,
      0))
      (fun p ->
      let (s,
           m) =
        Coq_Pos.sqrtrem
          p
      in
      (match m with
       | Coq_Pos.IsPos r ->
         (s,
           r)
       | _ ->
         (s,
           0)))
      n
  
  (** val sqrt :
      int
      ->
      int **)
  
  let sqrt n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ ->
      0)
      (fun p ->
      (Coq_Pos.sqrt
        p))
      n
  
  (** val coq_lor :
      int
      ->
      int
      ->
      int **)
  
  let coq_lor n m =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ ->
      m)
      (fun p ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ ->
        n)
        (fun q ->
        (Coq_Pos.coq_lor
          p
          q))
        m)
      n
  
  (** val coq_land :
      int
      ->
      int
      ->
      int **)
  
  let coq_land n m =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ ->
      0)
      (fun p ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ ->
        0)
        (fun q ->
        Coq_Pos.coq_land
          p
          q)
        m)
      n
  
  (** val ldiff :
      int
      ->
      int
      ->
      int **)
  
  let rec ldiff n m =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ ->
      0)
      (fun p ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ ->
        n)
        (fun q ->
        Coq_Pos.ldiff
          p
          q)
        m)
      n
  
  (** val coq_lxor :
      int
      ->
      int
      ->
      int **)
  
  let coq_lxor n m =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ ->
      m)
      (fun p ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ ->
        n)
        (fun q ->
        Coq_Pos.coq_lxor
          p
          q)
        m)
      n
  
  (** val shiftl_nat :
      int
      ->
      int
      ->
      int **)
  
  let shiftl_nat a n =
    nat_iter
      n
      double
      a
  
  (** val shiftr_nat :
      int
      ->
      int
      ->
      int **)
  
  let shiftr_nat a n =
    nat_iter
      n
      div2
      a
  
  (** val shiftl :
      int
      ->
      int
      ->
      int **)
  
  let shiftl a n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ ->
      0)
      (fun a0 ->
      (Coq_Pos.shiftl
        a0
        n))
      a
  
  (** val shiftr :
      int
      ->
      int
      ->
      int **)
  
  let shiftr a n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ ->
      a)
      (fun p ->
      Coq_Pos.iter
        p
        div2
        a)
      n
  
  (** val testbit_nat :
      int
      ->
      int
      ->
      bool **)
  
  let testbit_nat a =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ x ->
      false)
      (fun p ->
      Coq_Pos.testbit_nat
        p)
      a
  
  (** val testbit :
      int
      ->
      int
      ->
      bool **)
  
  let testbit a n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ ->
      false)
      (fun p ->
      Coq_Pos.testbit
        p
        n)
      a
  
  (** val to_nat :
      int
      ->
      int **)
  
  let to_nat a =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ ->
      0)
      (fun p ->
      Coq_Pos.to_nat
        p)
      a
  
  (** val of_nat :
      int
      ->
      int **)
  
  let of_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      0)
      (fun n' ->
      (Coq_Pos.of_succ_nat
        n'))
      n
  
  (** val iter :
      int
      ->
      ('a1
      ->
      'a1)
      ->
      'a1
      ->
      'a1 **)
  
  let iter n f x =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ ->
      x)
      (fun p ->
      Coq_Pos.iter
        p
        f
        x)
      n
  
  (** val eq_dec :
      int
      ->
      int
      ->
      bool **)
  
  let eq_dec n m =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ ->
        true)
        (fun p ->
        false)
        m)
      (fun x ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ ->
        false)
        (fun p0 ->
        Coq_Pos.eq_dec
          x
          p0)
        m)
      n
  
  (** val discr :
      int
      ->
      int
      option **)
  
  let discr n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ ->
      None)
      (fun p ->
      Some
      p)
      n
  
  (** val binary_rect :
      'a1
      ->
      (int
      ->
      'a1
      ->
      'a1)
      ->
      (int
      ->
      'a1
      ->
      'a1)
      ->
      int
      ->
      'a1 **)
  
  let binary_rect f0 f2 fS2 n =
    let f2' =
      fun p ->
      f2
        p
    in
    let fS2' =
      fun p ->
      fS2
        p
    in
    ((fun f0 fp n -> if n=0 then f0 () else fp n)
       (fun _ ->
       f0)
       (fun p ->
       let rec f p0 =
         (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
           (fun p1 ->
           fS2'
             p1
             (f
               p1))
           (fun p1 ->
           f2'
             p1
             (f
               p1))
           (fun _ ->
           fS2
             0
             f0)
           p0
       in f
            p)
       n)
  
  (** val binary_rec :
      'a1
      ->
      (int
      ->
      'a1
      ->
      'a1)
      ->
      (int
      ->
      'a1
      ->
      'a1)
      ->
      int
      ->
      'a1 **)
  
  let binary_rec =
    binary_rect
  
  (** val peano_rect :
      'a1
      ->
      (int
      ->
      'a1
      ->
      'a1)
      ->
      int
      ->
      'a1 **)
  
  let peano_rect f0 f n =
    let f' =
      fun p ->
      f
        p
    in
    ((fun f0 fp n -> if n=0 then f0 () else fp n)
       (fun _ ->
       f0)
       (fun p ->
       Coq_Pos.peano_rect
         (f
           0
           f0)
         f'
         p)
       n)
  
  (** val peano_rec :
      'a1
      ->
      (int
      ->
      'a1
      ->
      'a1)
      ->
      int
      ->
      'a1 **)
  
  let peano_rec =
    peano_rect
  
  (** val leb_spec0 :
      int
      ->
      int
      ->
      reflect **)
  
  let leb_spec0 x y =
    iff_reflect
      (leb
        x
        y)
  
  (** val ltb_spec0 :
      int
      ->
      int
      ->
      reflect **)
  
  let ltb_spec0 x y =
    iff_reflect
      (ltb
        x
        y)
  
  module Private_BootStrap = 
   struct 
    
   end
  
  (** val recursion :
      'a1
      ->
      (int
      ->
      'a1
      ->
      'a1)
      ->
      int
      ->
      'a1 **)
  
  let recursion x =
    peano_rect
      x
  
  module Private_OrderTac = 
   struct 
    module Elts = 
     struct 
      type t
        =
        int
     end
    
    module Tac = MakeOrderTac(Elts)
   end
  
  module Private_NZPow = 
   struct 
    
   end
  
  module Private_NZSqrt = 
   struct 
    
   end
  
  (** val sqrt_up :
      int
      ->
      int **)
  
  let sqrt_up a =
    match compare
            0
            a with
    | Lt ->
      succ
        (sqrt
          (pred
            a))
    | _ ->
      0
  
  (** val log2_up :
      int
      ->
      int **)
  
  let log2_up a =
    match compare
            1
            a with
    | Lt ->
      succ
        (log2
          (pred
            a))
    | _ ->
      0
  
  module Private_NZDiv = 
   struct 
    
   end
  
  (** val lcm :
      int
      ->
      int
      ->
      int **)
  
  let lcm a b =
    mul
      a
      (div
        b
        (gcd
          a
          b))
  
  (** val eqb_spec :
      int
      ->
      int
      ->
      reflect **)
  
  let eqb_spec x y =
    iff_reflect
      (eqb
        x
        y)
  
  (** val b2n :
      bool
      ->
      int **)
  
  let b2n = function
  | true ->
    1
  | false ->
    0
  
  (** val setbit :
      int
      ->
      int
      ->
      int **)
  
  let setbit a n =
    coq_lor
      a
      (shiftl
        1
        n)
  
  (** val clearbit :
      int
      ->
      int
      ->
      int **)
  
  let clearbit a n =
    ldiff
      a
      (shiftl
        1
        n)
  
  (** val ones :
      int
      ->
      int **)
  
  let ones n =
    pred
      (shiftl
        1
        n)
  
  (** val lnot :
      int
      ->
      int
      ->
      int **)
  
  let lnot a n =
    coq_lxor
      a
      (ones
        n)
  
  module Private_Tac = 
   struct 
    
   end
  
  module Private_Rev = 
   struct 
    module ORev = 
     struct 
      type t
        =
        int
     end
    
    module MRev = 
     struct 
      (** val max :
          int
          ->
          int
          ->
          int **)
      
      let max x y =
        min
          y
          x
     end
    
    module MPRev = MaxLogicalProperties(ORev)(MRev)
   end
  
  module Private_Dec = 
   struct 
    (** val max_case_strong :
        int
        ->
        int
        ->
        (int
        ->
        int
        ->
        __
        ->
        'a1
        ->
        'a1)
        ->
        (__
        ->
        'a1)
        ->
        (__
        ->
        'a1)
        ->
        'a1 **)
    
    let max_case_strong n m compat hl hr =
      let c =
        compSpec2Type
          n
          m
          (compare
            n
            m)
      in
      (match c with
       | CompGtT ->
         compat
           n
           (max
             n
             m)
           __
           (hl
             __)
       | _ ->
         compat
           m
           (max
             n
             m)
           __
           (hr
             __))
    
    (** val max_case :
        int
        ->
        int
        ->
        (int
        ->
        int
        ->
        __
        ->
        'a1
        ->
        'a1)
        ->
        'a1
        ->
        'a1
        ->
        'a1 **)
    
    let max_case n m x x0 x1 =
      max_case_strong
        n
        m
        x
        (fun _ ->
        x0)
        (fun _ ->
        x1)
    
    (** val max_dec :
        int
        ->
        int
        ->
        bool **)
    
    let max_dec n m =
      max_case
        n
        m
        (fun x y _ h0 ->
        h0)
        true
        false
    
    (** val min_case_strong :
        int
        ->
        int
        ->
        (int
        ->
        int
        ->
        __
        ->
        'a1
        ->
        'a1)
        ->
        (__
        ->
        'a1)
        ->
        (__
        ->
        'a1)
        ->
        'a1 **)
    
    let min_case_strong n m compat hl hr =
      let c =
        compSpec2Type
          n
          m
          (compare
            n
            m)
      in
      (match c with
       | CompGtT ->
         compat
           m
           (min
             n
             m)
           __
           (hr
             __)
       | _ ->
         compat
           n
           (min
             n
             m)
           __
           (hl
             __))
    
    (** val min_case :
        int
        ->
        int
        ->
        (int
        ->
        int
        ->
        __
        ->
        'a1
        ->
        'a1)
        ->
        'a1
        ->
        'a1
        ->
        'a1 **)
    
    let min_case n m x x0 x1 =
      min_case_strong
        n
        m
        x
        (fun _ ->
        x0)
        (fun _ ->
        x1)
    
    (** val min_dec :
        int
        ->
        int
        ->
        bool **)
    
    let min_dec n m =
      min_case
        n
        m
        (fun x y _ h0 ->
        h0)
        true
        false
   end
  
  (** val max_case_strong :
      int
      ->
      int
      ->
      (__
      ->
      'a1)
      ->
      (__
      ->
      'a1)
      ->
      'a1 **)
  
  let max_case_strong n m x x0 =
    Private_Dec.max_case_strong
      n
      m
      (fun x1 y _ x2 ->
      x2)
      x
      x0
  
  (** val max_case :
      int
      ->
      int
      ->
      'a1
      ->
      'a1
      ->
      'a1 **)
  
  let max_case n m x x0 =
    max_case_strong
      n
      m
      (fun _ ->
      x)
      (fun _ ->
      x0)
  
  (** val max_dec :
      int
      ->
      int
      ->
      bool **)
  
  let max_dec =
    Private_Dec.max_dec
  
  (** val min_case_strong :
      int
      ->
      int
      ->
      (__
      ->
      'a1)
      ->
      (__
      ->
      'a1)
      ->
      'a1 **)
  
  let min_case_strong n m x x0 =
    Private_Dec.min_case_strong
      n
      m
      (fun x1 y _ x2 ->
      x2)
      x
      x0
  
  (** val min_case :
      int
      ->
      int
      ->
      'a1
      ->
      'a1
      ->
      'a1 **)
  
  let min_case n m x x0 =
    min_case_strong
      n
      m
      (fun _ ->
      x)
      (fun _ ->
      x0)
  
  (** val min_dec :
      int
      ->
      int
      ->
      bool **)
  
  let min_dec =
    Private_Dec.min_dec
 end

module Z = 
 struct 
  type t
    =
    int
  
  (** val zero :
      int **)
  
  let zero =
    0
  
  (** val one :
      int **)
  
  let one =
    1
  
  (** val two :
      int **)
  
  let two =
    ((fun p->2*p)
      1)
  
  (** val double :
      int
      ->
      int **)
  
  let double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ ->
      0)
      (fun p ->
      ((fun p->2*p)
      p))
      (fun p ->
      (~-)
      ((fun p->2*p)
      p))
      x
  
  (** val succ_double :
      int
      ->
      int **)
  
  let succ_double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ ->
      1)
      (fun p ->
      ((fun p->1+2*p)
      p))
      (fun p ->
      (~-)
      (Coq_Pos.pred_double
        p))
      x
  
  (** val pred_double :
      int
      ->
      int **)
  
  let pred_double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ ->
      (~-)
      1)
      (fun p ->
      (Coq_Pos.pred_double
        p))
      (fun p ->
      (~-)
      ((fun p->1+2*p)
      p))
      x
  
  (** val pos_sub :
      int
      ->
      int
      ->
      int **)
  
  let rec pos_sub x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q ->
        double
          (pos_sub
            p
            q))
        (fun q ->
        succ_double
          (pos_sub
            p
            q))
        (fun _ ->
        ((fun p->2*p)
        p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q ->
        pred_double
          (pos_sub
            p
            q))
        (fun q ->
        double
          (pos_sub
            p
            q))
        (fun _ ->
        (Coq_Pos.pred_double
          p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q ->
        (~-)
        ((fun p->2*p)
        q))
        (fun q ->
        (~-)
        (Coq_Pos.pred_double
          q))
        (fun _ ->
        0)
        y)
      x
  
  (** val add :
      int
      ->
      int
      ->
      int **)
  
  let add = (+)
  
  (** val opp :
      int
      ->
      int **)
  
  let opp = (~-)
  
  (** val succ :
      int
      ->
      int **)
  
  let succ = succ
  
  (** val pred :
      int
      ->
      int **)
  
  let pred = pred
  
  (** val sub :
      int
      ->
      int
      ->
      int **)
  
  let sub = (-)
  
  (** val mul :
      int
      ->
      int
      ->
      int **)
  
  let mul = ( * )
  
  (** val pow_pos :
      int
      ->
      int
      ->
      int **)
  
  let pow_pos z n =
    Coq_Pos.iter
      n
      (mul
        z)
      1
  
  (** val pow :
      int
      ->
      int
      ->
      int **)
  
  let pow x y =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ ->
      1)
      (fun p ->
      pow_pos
        x
        p)
      (fun p ->
      0)
      y
  
  (** val square :
      int
      ->
      int **)
  
  let square x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ ->
      0)
      (fun p ->
      (Coq_Pos.square
        p))
      (fun p ->
      (Coq_Pos.square
        p))
      x
  
  (** val compare :
      int
      ->
      int
      ->
      comparison **)
  
  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt
  
  (** val sgn : int -> int **)
  
  let sgn z =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ ->
      0)
      (fun p ->
      1)
      (fun p -> (~-)
      1)
      z
  
  (** val leb : int -> int -> bool **)
  
  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true
  
  (** val ltb : int -> int -> bool **)
  
  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false
  
  (** val geb : int -> int -> bool **)
  
  let geb x y =
    match compare x y with
    | Lt -> false
    | _ -> true
  
  (** val gtb : int -> int -> bool **)
  
  let gtb x y =
    match compare x y with
    | Gt -> true
    | _ -> false
  
  (** val eqb : int -> int -> bool **)
  
  let rec eqb x y =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ ->
        true)
        (fun p ->
        false)
        (fun p ->
        false)
        y)
      (fun p ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ ->
        false)
        (fun q ->
        Coq_Pos.eqb p q)
        (fun p0 ->
        false)
        y)
      (fun p ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ ->
        false)
        (fun p0 ->
        false)
        (fun q ->
        Coq_Pos.eqb p q)
        y)
      x
  
  (** val max : int -> int -> int **)
  
  let max = max
  
  (** val min : int -> int -> int **)
  
  let min = min
  
  (** val abs : int -> int **)
  
  let abs = abs
  
  (** val abs_nat : int -> int **)
  
  let abs_nat z =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ ->
      0)
      (fun p ->
      Coq_Pos.to_nat p)
      (fun p ->
      Coq_Pos.to_nat p)
      z
  
  (** val abs_N : int -> int **)
  
  let abs_N = abs
  
  (** val to_nat : int -> int **)
  
  let to_nat z =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ ->
      0)
      (fun p ->
      Coq_Pos.to_nat p)
      (fun p ->
      0)
      z
  
  (** val to_N : int -> int **)
  
  let to_N z =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ ->
      0)
      (fun p ->
      p)
      (fun p ->
      0)
      z
  
  (** val of_nat : int -> int **)
  
  let of_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      0)
      (fun n0 ->
      (Coq_Pos.of_succ_nat n0))
      n
  
  (** val of_N : int -> int **)
  
  let of_N = fun p -> p
  
  (** val to_pos : int -> int **)
  
  let to_pos z =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ ->
      1)
      (fun p ->
      p)
      (fun p ->
      1)
      z
  
  (** val iter : int -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)
  
  let iter n f x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ ->
      x)
      (fun p ->
      Coq_Pos.iter p f x)
      (fun p ->
      x)
      n
  
  (** val pos_div_eucl : int -> int -> int * int **)
  
  let rec pos_div_eucl a b =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = add (mul ((fun p->2*p) 1) r) 1 in
      if ltb r' b
      then ((mul ((fun p->2*p) 1) q), r')
      else ((add (mul ((fun p->2*p) 1) q) 1), (sub r' b)))
      (fun a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = mul ((fun p->2*p) 1) r in
      if ltb r' b
      then ((mul ((fun p->2*p) 1) q), r')
      else ((add (mul ((fun p->2*p) 1) q) 1), (sub r' b)))
      (fun _ ->
      if leb ((fun p->2*p) 1) b then (0, 1) else (1, 0))
      a
  
  (** val div_eucl : int -> int -> int * int **)
  
  let div_eucl a b =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> (0,
      0))
      (fun a' ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> (0,
        0))
        (fun p ->
        pos_div_eucl a' b)
        (fun b' ->
        let (q, r) = pos_div_eucl a' b' in
        ((fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
           (fun _ -> ((opp q),
           0))
           (fun p -> ((opp (add q 1)),
           (add b r)))
           (fun p -> ((opp (add q 1)),
           (add b r)))
           r))
        b)
      (fun a' ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> (0,
        0))
        (fun p ->
        let (q, r) = pos_div_eucl a' b in
        ((fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
           (fun _ -> ((opp q),
           0))
           (fun p0 -> ((opp (add q 1)),
           (sub b r)))
           (fun p0 -> ((opp (add q 1)),
           (sub b r)))
           r))
        (fun b' ->
        let (q, r) = pos_div_eucl a' b' in (q, (opp r)))
        b)
      a
  
  (** val div : int -> int -> int **)
  
  let div a b =
    let (q, x) = div_eucl a b in q
  
  (** val modulo : int -> int -> int **)
  
  let modulo a b =
    let (x, r) = div_eucl a b in r
  
  (** val quotrem : int -> int -> int * int **)
  
  let quotrem a b =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> (0,
      0))
      (fun a0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> (0,
        a))
        (fun b0 ->
        let (q, r) = N.pos_div_eucl a0 b0 in ((of_N q), (of_N r)))
        (fun b0 ->
        let (q, r) = N.pos_div_eucl a0 b0 in ((opp (of_N q)), (of_N r)))
        b)
      (fun a0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> (0,
        a))
        (fun b0 ->
        let (q, r) = N.pos_div_eucl a0 b0 in ((opp (of_N q)), (opp (of_N r))))
        (fun b0 ->
        let (q, r) = N.pos_div_eucl a0 b0 in ((of_N q), (opp (of_N r))))
        b)
      a
  
  (** val quot : int -> int -> int **)
  
  let quot a b =
    fst (quotrem a b)
  
  (** val rem : int -> int -> int **)
  
  let rem a b =
    snd (quotrem a b)
  
  (** val even : int -> bool **)
  
  let even z =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ ->
      true)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p0 ->
        false)
        (fun p0 ->
        true)
        (fun _ ->
        false)
        p)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p0 ->
        false)
        (fun p0 ->
        true)
        (fun _ ->
        false)
        p)
      z
  
  (** val odd : int -> bool **)
  
  let odd z =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ ->
      false)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p0 ->
        true)
        (fun p0 ->
        false)
        (fun _ ->
        true)
        p)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p0 ->
        true)
        (fun p0 ->
        false)
        (fun _ ->
        true)
        p)
      z
  
  (** val div2 : int -> int **)
  
  let div2 z =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ ->
      0)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p0 ->
        (Coq_Pos.div2 p))
        (fun p0 ->
        (Coq_Pos.div2 p))
        (fun _ ->
        0)
        p)
      (fun p -> (~-)
      (Coq_Pos.div2_up p))
      z
  
  (** val quot2 : int -> int **)
  
  let quot2 z =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ ->
      0)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p0 ->
        (Coq_Pos.div2 p))
        (fun p0 ->
        (Coq_Pos.div2 p))
        (fun _ ->
        0)
        p)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p0 -> (~-)
        (Coq_Pos.div2 p))
        (fun p0 -> (~-)
        (Coq_Pos.div2 p))
        (fun _ ->
        0)
        p)
      z
  
  (** val log2 : int -> int **)
  
  let log2 z =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ ->
      0)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p ->
        (Coq_Pos.size p))
        (fun p ->
        (Coq_Pos.size p))
        (fun _ ->
        0)
        p0)
      (fun p ->
      0)
      z
  
  (** val sqrtrem : int -> int * int **)
  
  let sqrtrem n =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> (0,
      0))
      (fun p ->
      let (s, m) = Coq_Pos.sqrtrem p in
      (match m with
       | Coq_Pos.IsPos r -> (s, r)
       | _ -> (s, 0)))
      (fun p -> (0,
      0))
      n
  
  (** val sqrt : int -> int **)
  
  let sqrt n =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ ->
      0)
      (fun p ->
      (Coq_Pos.sqrt p))
      (fun p ->
      0)
      n
  
  (** val gcd : int -> int -> int **)
  
  let gcd a b =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ ->
      abs b)
      (fun a0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ ->
        abs a)
        (fun b0 ->
        (Coq_Pos.gcd a0 b0))
        (fun b0 ->
        (Coq_Pos.gcd a0 b0))
        b)
      (fun a0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ ->
        abs a)
        (fun b0 ->
        (Coq_Pos.gcd a0 b0))
        (fun b0 ->
        (Coq_Pos.gcd a0 b0))
        b)
      a
  
  (** val ggcd : int -> int -> int * (int * int) **)
  
  let ggcd a b =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> ((abs b), (0,
      (sgn b))))
      (fun a0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> ((abs a), ((sgn a),
        0)))
        (fun b0 ->
        let (g, p) = Coq_Pos.ggcd a0 b0 in let (aa, bb) = p in (g, (aa, bb)))
        (fun b0 ->
        let (g, p) = Coq_Pos.ggcd a0 b0 in
        let (aa, bb) = p in (g, (aa, ((~-) bb))))
        b)
      (fun a0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> ((abs a), ((sgn a),
        0)))
        (fun b0 ->
        let (g, p) = Coq_Pos.ggcd a0 b0 in
        let (aa, bb) = p in (g, (((~-) aa), bb)))
        (fun b0 ->
        let (g, p) = Coq_Pos.ggcd a0 b0 in
        let (aa, bb) = p in (g, (((~-) aa), ((~-) bb))))
        b)
      a
  
  (** val testbit : int -> int -> bool **)
  
  let testbit a n =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ ->
      odd a)
      (fun p ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ ->
        false)
        (fun a0 ->
        Coq_Pos.testbit a0 p)
        (fun a0 ->
        negb (N.testbit (Coq_Pos.pred_N a0) p))
        a)
      (fun p ->
      false)
      n
  
  (** val shiftl : int -> int -> int **)
  
  let shiftl a n =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ ->
      a)
      (fun p ->
      Coq_Pos.iter p (mul ((fun p->2*p) 1)) a)
      (fun p ->
      Coq_Pos.iter p div2 a)
      n
  
  (** val shiftr : int -> int -> int **)
  
  let shiftr a n =
    shiftl a (opp n)
  
  (** val coq_lor : int -> int -> int **)
  
  let coq_lor a b =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ ->
      b)
      (fun a0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ ->
        a)
        (fun b0 ->
        (Coq_Pos.coq_lor a0 b0))
        (fun b0 -> (~-)
        (N.succ_pos (N.ldiff (Coq_Pos.pred_N b0) a0)))
        b)
      (fun a0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ ->
        a)
        (fun b0 -> (~-)
        (N.succ_pos (N.ldiff (Coq_Pos.pred_N a0) b0)))
        (fun b0 -> (~-)
        (N.succ_pos (N.coq_land (Coq_Pos.pred_N a0) (Coq_Pos.pred_N b0))))
        b)
      a
  
  (** val coq_land : int -> int -> int **)
  
  let coq_land a b =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ ->
      0)
      (fun a0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ ->
        0)
        (fun b0 ->
        of_N (Coq_Pos.coq_land a0 b0))
        (fun b0 ->
        of_N (N.ldiff a0 (Coq_Pos.pred_N b0)))
        b)
      (fun a0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ ->
        0)
        (fun b0 ->
        of_N (N.ldiff b0 (Coq_Pos.pred_N a0)))
        (fun b0 -> (~-)
        (N.succ_pos (N.coq_lor (Coq_Pos.pred_N a0) (Coq_Pos.pred_N b0))))
        b)
      a
  
  (** val ldiff : int -> int -> int **)
  
  let ldiff a b =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ ->
      0)
      (fun a0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ ->
        a)
        (fun b0 ->
        of_N (Coq_Pos.ldiff a0 b0))
        (fun b0 ->
        of_N (N.coq_land a0 (Coq_Pos.pred_N b0)))
        b)
      (fun a0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ ->
        a)
        (fun b0 -> (~-)
        (N.succ_pos (N.coq_lor (Coq_Pos.pred_N a0) b0)))
        (fun b0 ->
        of_N (N.ldiff (Coq_Pos.pred_N b0) (Coq_Pos.pred_N a0)))
        b)
      a
  
  (** val coq_lxor : int -> int -> int **)
  
  let coq_lxor a b =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ ->
      b)
      (fun a0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ ->
        a)
        (fun b0 ->
        of_N (Coq_Pos.coq_lxor a0 b0))
        (fun b0 -> (~-)
        (N.succ_pos (N.coq_lxor a0 (Coq_Pos.pred_N b0))))
        b)
      (fun a0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ ->
        a)
        (fun b0 -> (~-)
        (N.succ_pos (N.coq_lxor (Coq_Pos.pred_N a0) b0)))
        (fun b0 ->
        of_N (N.coq_lxor (Coq_Pos.pred_N a0) (Coq_Pos.pred_N b0)))
        b)
      a
  
  (** val eq_dec : int -> int -> bool **)
  
  let eq_dec x y =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ ->
        true)
        (fun p ->
        false)
        (fun p ->
        false)
        y)
      (fun x0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ ->
        false)
        (fun p0 ->
        Coq_Pos.eq_dec x0 p0)
        (fun p0 ->
        false)
        y)
      (fun x0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ ->
        false)
        (fun p0 ->
        false)
        (fun p0 ->
        Coq_Pos.eq_dec x0 p0)
        y)
      x
  
  module Private_BootStrap = 
   struct 
    
   end
  
  (** val leb_spec0 : int -> int -> reflect **)
  
  let leb_spec0 x y =
    iff_reflect (leb x y)
  
  (** val ltb_spec0 : int -> int -> reflect **)
  
  let ltb_spec0 x y =
    iff_reflect (ltb x y)
  
  module Private_OrderTac = 
   struct 
    module Elts = 
     struct 
      type t = int
     end
    
    module Tac = MakeOrderTac(Elts)
   end
  
  (** val sqrt_up : int -> int **)
  
  let sqrt_up a =
    match compare 0 a with
    | Lt -> succ (sqrt (pred a))
    | _ -> 0
  
  (** val log2_up : int -> int **)
  
  let log2_up a =
    match compare 1 a with
    | Lt -> succ (log2 (pred a))
    | _ -> 0
  
  module Private_NZDiv = 
   struct 
    
   end
  
  module Private_Div = 
   struct 
    module Quot2Div = 
     struct 
      (** val div : int -> int -> int **)
      
      let div =
        quot
      
      (** val modulo : int -> int -> int **)
      
      let modulo =
        rem
     end
    
    module NZQuot = 
     struct 
      
     end
   end
  
  (** val lcm : int -> int -> int **)
  
  let lcm a b =
    abs (mul a (div b (gcd a b)))
  
  (** val eqb_spec : int -> int -> reflect **)
  
  let eqb_spec x y =
    iff_reflect (eqb x y)
  
  (** val b2z : bool -> int **)
  
  let b2z = function
  | true -> 1
  | false -> 0
  
  (** val setbit : int -> int -> int **)
  
  let setbit a n =
    coq_lor a (shiftl 1 n)
  
  (** val clearbit : int -> int -> int **)
  
  let clearbit a n =
    ldiff a (shiftl 1 n)
  
  (** val lnot : int -> int **)
  
  let lnot a =
    pred (opp a)
  
  (** val ones : int -> int **)
  
  let ones n =
    pred (shiftl 1 n)
  
  module Private_Tac = 
   struct 
    
   end
  
  module Private_Rev = 
   struct 
    module ORev = 
     struct 
      type t = int
     end
    
    module MRev = 
     struct 
      (** val max : int -> int -> int **)
      
      let max x y =
        min y x
     end
    
    module MPRev = MaxLogicalProperties(ORev)(MRev)
   end
  
  module Private_Dec = 
   struct 
    (** val max_case_strong :
        int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__
        -> 'a1) -> 'a1 **)
    
    let max_case_strong n m compat hl hr =
      let c = compSpec2Type n m (compare n m) in
      (match c with
       | CompGtT -> compat n (max n m) __ (hl __)
       | _ -> compat m (max n m) __ (hr __))
    
    (** val max_case :
        int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)
    
    let max_case n m x x0 x1 =
      max_case_strong n m x (fun _ -> x0) (fun _ -> x1)
    
    (** val max_dec : int -> int -> bool **)
    
    let max_dec n m =
      max_case n m (fun x y _ h0 -> h0) true false
    
    (** val min_case_strong :
        int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__
        -> 'a1) -> 'a1 **)
    
    let min_case_strong n m compat hl hr =
      let c = compSpec2Type n m (compare n m) in
      (match c with
       | CompGtT -> compat m (min n m) __ (hr __)
       | _ -> compat n (min n m) __ (hl __))
    
    (** val min_case :
        int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)
    
    let min_case n m x x0 x1 =
      min_case_strong n m x (fun _ -> x0) (fun _ -> x1)
    
    (** val min_dec : int -> int -> bool **)
    
    let min_dec n m =
      min_case n m (fun x y _ h0 -> h0) true false
   end
  
  (** val max_case_strong :
      int -> int -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
  
  let max_case_strong n m x x0 =
    Private_Dec.max_case_strong n m (fun x1 y _ x2 -> x2) x x0
  
  (** val max_case : int -> int -> 'a1 -> 'a1 -> 'a1 **)
  
  let max_case n m x x0 =
    max_case_strong n m (fun _ -> x) (fun _ -> x0)
  
  (** val max_dec : int -> int -> bool **)
  
  let max_dec =
    Private_Dec.max_dec
  
  (** val min_case_strong :
      int -> int -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
  
  let min_case_strong n m x x0 =
    Private_Dec.min_case_strong n m (fun x1 y _ x2 -> x2) x x0
  
  (** val min_case : int -> int -> 'a1 -> 'a1 -> 'a1 **)
  
  let min_case n m x x0 =
    min_case_strong n m (fun _ -> x) (fun _ -> x0)
  
  (** val min_dec : int -> int -> bool **)
  
  let min_dec =
    Private_Dec.min_dec
 end

type 'a predb = 'a -> bool

(** val or0 : bool -> bool -> bool **)

let or0 x y =
  if x then true else y

(** val neg : bool -> bool **)

let neg = function
| true -> false
| false -> true

type decidable =
  bool
  (* singleton inductive, whose constructor was decidable_make *)

type 'a comparable =
  'a -> 'a -> decidable
  (* singleton inductive, whose constructor was make_comparable *)

(** val bool_comparable : bool comparable **)

let bool_comparable =
  failwith "AXIOM TO BE REALIZED"

(** val my_Z_of_nat : int -> int **)

let my_Z_of_nat =
  Z.of_nat

(** val fold_right : ('a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 list -> 'a2 **)

let rec fold_right f acc = function
| [] -> acc
| x :: l' -> f x (fold_right f acc l')

(** val fold_left : ('a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 list -> 'a2 **)

let rec fold_left f acc = function
| [] -> acc
| x :: l' -> fold_left f (f x acc) l'

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let map f =
  fold_right (fun x acc -> (f x) :: acc) []

(** val filter : 'a1 predb -> 'a1 list -> 'a1 list **)

let filter f =
  fold_right (fun x acc -> if f x then x :: acc else acc) []

(** val append : 'a1 list -> 'a1 list -> 'a1 list **)

let append l1 l2 =
  fold_right (fun x acc -> x :: acc) l2 l1

(** val rev : 'a1 list -> 'a1 list **)

let rev l =
  fold_left (fun x acc -> x :: acc) [] l

(** val split : ('a1 * 'a2) list -> 'a1 list * 'a2 list **)

let rec split = function
| [] -> ([], [])
| p :: l' ->
  let (a, b) = p in let (la, lb) = split l' in ((a :: la), (b :: lb))

(** val append0 : char list -> char list -> char list **)

let rec append0 s1 s2 =
  match s1 with
  | [] -> s2
  | c::s1' -> c::(append0 s1' s2)

(** val string_comparable : char list comparable **)

let string_comparable =
  failwith "AXIOM TO BE REALIZED"

(** val and_decidable : decidable -> decidable -> decidable **)

let and_decidable =
  failwith "AXIOM TO BE REALIZED"

(** val in_decidable : 'a1 comparable -> 'a1 -> 'a1 list -> decidable **)

let in_decidable =
  failwith "AXIOM TO BE REALIZED"

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

module HeapList = 
 struct 
  type ('k, 'v) heap = ('k * 'v) list
  
  (** val empty : ('a1, 'a2) heap **)
  
  let empty =
    []
  
  (** val to_list : ('a1, 'a2) heap -> ('a1, 'a2) heap **)
  
  let to_list l =
    l
  
  (** val assoc : 'a1 comparable -> 'a1 -> ('a1 * 'a2) list -> 'a2 **)
  
  let rec assoc h1 k = function
  | [] -> (raise Not_found) __
  | p :: l' -> let (x, v) = p in if h1 x k then v else assoc h1 k l'
  
  (** val read : 'a1 comparable -> ('a1, 'a2) heap -> 'a1 -> 'a2 **)
  
  let read h l k =
    assoc h k l
  
  (** val write : ('a1, 'a2) heap -> 'a1 -> 'a2 -> ('a1 * 'a2) list **)
  
  let write l k v =
    (k, v) :: l
  
  (** val rem :
      'a1 comparable -> ('a1, 'a2) heap -> 'a1 -> ('a1 * 'a2) list **)
  
  let rem h1 l k =
    filter (fun p -> h1 (fst p) k) l
  
  (** val read_option :
      'a1 comparable -> ('a1, 'a2) heap -> 'a1 -> 'a2 option **)
  
  let rec read_option h l k =
    match l with
    | [] -> None
    | p :: l' ->
      let (x, v) = p in if h x k then Some v else read_option h l' k
  
  (** val mem_assoc : 'a2 comparable -> 'a2 -> ('a2 * 'a1) list -> bool **)
  
  let rec mem_assoc h1 k = function
  | [] -> false
  | p :: l' -> let (x, y) = p in or0 (h1 x k) (mem_assoc h1 k l')
  
  (** val indom_dec : 'a1 comparable -> ('a1, 'a2) heap -> 'a1 -> bool **)
  
  let indom_dec h1 h k =
    mem_assoc h1 k h
  
  (** val indom_decidable :
      'a1 comparable -> ('a1, 'a2) heap -> 'a1 -> decidable **)
  
  let indom_decidable =
    failwith "AXIOM TO BE REALIZED"
 end

type binary64 = float

type number = binary64

(** val number_of_int : int -> number **)

let number_of_int = float_of_int

(** val number_add : number -> number -> number **)

let number_add = (+.)

(** val number_mult : number -> number -> number **)

let number_mult = ( *. )

(** val number_div : number -> number -> number **)

let number_div = (/.)

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

(** val field_normal_prototype : field **)

let field_normal_prototype =
  Field_normal
    ('p'::('r'::('o'::('t'::('o'::('t'::('y'::('p'::('e'::[])))))))))

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

module Heap = HeapList

type heap0 = (ref, value) Heap.heap

(** val loc_comparable : loc comparable **)

let loc_comparable =
  failwith "AXIOM TO BE REALIZED"

(** val ref_comparable : ref comparable **)

let ref_comparable =
  failwith "AXIOM TO BE REALIZED"

(** val number_comparable : number comparable **)

let number_comparable = (=)

(** val value_compare : value -> value -> bool **)

let value_compare v1 v2 =
  match v1 with
  | Value_undef ->
    (match v2 with
     | Value_undef -> true
     | _ -> false)
  | Value_bool b1 ->
    (match v2 with
     | Value_bool b2 -> bool_comparable b1 b2
     | _ -> false)
  | Value_number n1 ->
    (match v2 with
     | Value_number n2 -> number_comparable n1 n2
     | _ -> false)
  | Value_string s1 ->
    (match v2 with
     | Value_string s2 -> string_comparable s1 s2
     | _ -> false)
  | Value_loc l1 ->
    (match v2 with
     | Value_loc l2 -> loc_comparable l1 l2
     | _ -> false)
  | _ -> false

(** val empty_heap : heap0 **)

let empty_heap =
  Heap.empty

(** val write0 : heap0 -> loc -> field -> value -> (ref, value) Heap.heap **)

let write0 h l f v =
  Heap.write h (Ref (l, f)) v

(** val write_fields : heap0 -> loc -> (field * value) list -> heap0 **)

let write_fields h l fvs =
  fold_left (fun fv acc -> let (f, v) = fv in write0 acc l f v) h fvs

(** val write_proto : heap0 -> loc -> loc -> (ref, value) Heap.heap **)

let write_proto h l l' =
  write0 h l Field_proto (Value_loc l')

(** val write_this : heap0 -> loc -> loc -> (ref, value) Heap.heap **)

let write_this h l l' =
  write0 h l Field_this (Value_loc l')

(** val read0 : heap0 -> loc -> field -> value **)

let read0 h l f =
  Heap.read ref_comparable h (Ref (l, f))

(** val rem0 : heap0 -> loc -> field -> (ref, value) Heap.heap **)

let rem0 h l f =
  Heap.rem ref_comparable h (Ref (l, f))

(** val update : heap0 -> loc -> field -> value -> (ref, value) Heap.heap **)

let update h l f v =
  let l' = if loc_comparable l Loc_null then Loc_global else l in
  write0 h l' f v

(** val dealloc : heap0 -> result -> heap0 **)

let dealloc h = function
| Result_value v -> h
| Result_ref r0 -> let Ref (l, f) = r0 in rem0 h l f

(** val init_heap : (ref, value) Heap.heap **)

let init_heap =
  let h1 = write_proto empty_heap Loc_global Loc_obj_proto in
  let h2 = write_proto h1 Loc_obj_proto Loc_null in
  let h3 = write_proto h2 Loc_func_proto Loc_obj_proto in
  let h4 = write_proto h3 Loc_scope Loc_null in
  write_this h4 Loc_scope Loc_global

(** val init_scope : loc list **)

let init_scope =
  Loc_global :: (Loc_scope :: [])

(** val value_of_literal : literal -> value **)

let value_of_literal = function
| Literal_null -> Value_loc Loc_null
| Literal_bool b -> Value_bool b
| Literal_number m -> Value_number m
| Literal_string g -> Value_string g

(** val get_this : heap0 -> result -> loc **)

let get_this h = function
| Result_value v -> Loc_global
| Result_ref r0 ->
  let Ref (l, n) = r0 in
  if HeapList.indom_decidable ref_comparable h (Ref (l, Field_this))
  then Loc_global
  else l

(** val alloc_obj : heap0 -> loc -> loc -> (ref, value) Heap.heap **)

let alloc_obj h l l' =
  write_proto h l l'

(** val alloc_fun :
    heap0 -> loc -> scope -> char list list -> expr -> loc -> heap0 **)

let alloc_fun h l' s lx e l =
  write_fields h l' ((Field_proto, (Value_loc
    Loc_func_proto)) :: ((field_normal_prototype, (Value_loc
    l)) :: ((Field_scope, (Value_scope s)) :: ((Field_body, (Value_body (lx,
    e))) :: []))))

(** val reserve_local_vars : heap0 -> loc -> char list list -> heap0 **)

let reserve_local_vars h l ys =
  write_fields h l (map (fun y -> ((Field_normal y), Value_undef)) ys)

(** val obj_of_value : value -> loc -> loc **)

let obj_of_value v l =
  match v with
  | Value_loc l1 -> if loc_comparable l1 Loc_null then l else l1
  | _ -> l

(** val obj_or_glob_of_value : value -> loc **)

let obj_or_glob_of_value v =
  obj_of_value v Loc_obj_proto

(** val defs : char list list -> expr -> char list list **)

let rec defs lx e =
  let d = defs lx in
  (match e with
   | Expr_seq (e1, e2) -> append (d e1) (d e2)
   | Expr_var_decl (y, oe) ->
     if in_decidable string_comparable y lx then [] else y :: []
   | Expr_if (e1, e2, o) ->
     (match o with
      | Some e3 -> append (d e2) (d e3)
      | None -> d e2)
   | Expr_while (e1, e2) -> d e2
   | Expr_with (e1, e2) -> d e2
   | _ -> [])

(** val indom_decidable0 : heap0 -> loc -> field -> decidable **)

let indom_decidable0 =
  failwith "AXIOM TO BE REALIZED"

(** val fresh_for_list : (ref * value) list -> loc **)

let fresh_for_list h =
  Loc_normal (succ
    (fold_left (fun r n ->
      let (y, y0) = r in
      let Ref (l, f) = y in
      (match l with
       | Loc_normal n' -> max n n'
       | _ -> n)) 0 h))

(** val fresh_for :
    heap0
    ->
    loc **)

let fresh_for = fresh_for_list

(** val basic_value_decidable :
    value
    ->
    decidable **)

let basic_value_decidable =
  failwith "AXIOM TO BE REALIZED"

(** val proto_comp_body :
    (heap0
    ->
    field
    ->
    loc
    ->
    loc)
    ->
    heap0
    ->
    field
    ->
    loc
    ->
    loc **)

let proto_comp_body proto_comp0 h f l =
  if loc_comparable
       l
       Loc_null
  then Loc_null
  else if indom_decidable0
            h
            l
            f
       then l
       else if indom_decidable0
                 h
                 l
                 Field_proto
            then (match read0
                          h
                          l
                          Field_proto with
                  | Value_loc l' ->
                    proto_comp0
                      h
                      f
                      l'
                  | _ ->
                    (raise Not_found)
                      __)
            else (raise Not_found)
                   __

(** val proto_comp :
    heap0
    ->
    field
    ->
    loc
    ->
    loc **)

let proto_comp x x0 x1 =
  (fun bigf -> let rec f x = bigf f x in f)
    (fun f' p ->
    let (p0,
         x3) =
      p
    in
    let (x2,
         x4) =
      p0
    in
    proto_comp_body
      (fun x5 x6 x7 ->
      f'
        ((x5,
        x6),
        x7))
      x2
      x4
      x3)
    ((x,
    x0),
    x1)

(** val scope_comp :
    heap0
    ->
    field
    ->
    scope
    ->
    loc **)

let rec scope_comp h f = function
| [] ->
  Loc_null
| l0 :: s ->
  let l' =
    proto_comp
      h
      f
      l0
  in
  if loc_comparable
       l'
       Loc_null
  then scope_comp
         h
         f
         s
  else l0

(** val getvalue_comp :
    heap0
    ->
    result
    ->
    value
    option **)

let getvalue_comp h = function
| Result_value v ->
  Some
    v
| Result_ref r0 ->
  let Ref (l,
           f) =
    r0
  in
  (match f with
   | Field_normal s ->
     if loc_comparable
          l
          Loc_null
     then None
     else let l' =
            proto_comp
              h
              f
              l
          in
          if loc_comparable
               l'
               Loc_null
          then Some
                 Value_undef
          else Some
                 (read0
                   h
                   l'
                   f)
   | _ ->
     None)

(** val mnostuck :
    bool **)

let mnostuck = true

type ret =
| Ret_result of result
| Ret_exn of result

type out =
| Out_return of heap0
   * ret
| Out_unspec
| Out_bottom

(** val make_error :
    heap0
    ->
    char list
    ->
    out **)

let make_error h s =
  Out_return
    (h,
    (Ret_exn
    (Result_value
    (Value_string
    s))))

(** val ret_ref :
    loc
    ->
    field
    ->
    ret **)

let ret_ref l f =
  Ret_result
    (Result_ref
    (Ref
    (l,
    f)))

(** val wrong :
    heap0
    ->
    out **)

let wrong h =
  if mnostuck
  then make_error
         h
         ('N'::('o'::(' '::('r'::('e'::('d'::('u'::('c'::('t'::('i'::('o'::('n'::(' '::('r'::('u'::('l'::('e'::(' '::('c'::('a'::('n'::(' '::('b'::('e'::(' '::('a'::('p'::('p'::('l'::('i'::('e'::('d'::('.'::[])))))))))))))))))))))))))))))))))
  else Out_unspec

(** val if_success :
    out
    ->
    (heap0
    ->
    result
    ->
    out)
    ->
    out **)

let if_success o k =
  match o with
  | Out_return (h,
                r) ->
    (match r with
     | Ret_result v ->
       k
         h
         v
     | Ret_exn r0 ->
       o)
  | _ ->
    o

(** val if_defined :
    heap0
    ->
    'a1
    option
    ->
    ('a1
    ->
    out)
    ->
    out **)

let if_defined h o k =
  match o with
  | Some a ->
    k
      a
  | None ->
    wrong
      h

(** val if_success_value :
    out
    ->
    (heap0
    ->
    value
    ->
    out)
    ->
    out **)

let if_success_value o k =
  if_success
    o
    (fun h1 r1 ->
    if_defined
      h1
      (getvalue_comp
        h1
        r1)
      (k
        h1))

(** val if_is_ref :
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
    out **)

let if_is_ref h r k =
  match r with
  | Result_value v ->
    wrong
      h
  | Result_ref r0 ->
    let Ref (l,
             f) =
      r0
    in
    k
      l
      f

(** val if_is_field_normal :
    heap0
    ->
    field
    ->
    (char list
    ->
    out)
    ->
    out **)

let if_is_field_normal h f k =
  match f with
  | Field_normal f0 ->
    k
      f0
  | _ ->
    wrong
      h

(** val if_eq :
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
    out **)

let if_eq l0 h o k1 k2 =
  if_defined
    h
    o
    (fun v ->
    match v with
    | Value_loc l ->
      if loc_comparable
           l
           l0
      then k1
             __
      else k2
             l
    | _ ->
      wrong
        h)

(** val if_not_eq :
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
    out **)

let if_not_eq l0 h o k =
  if_eq
    l0
    h
    o
    (fun _ ->
    wrong
      h)
    k

(** val if_is_null_ref :
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
    out **)

let if_is_null_ref r k1 k2 =
  match r with
  | Result_value v ->
    k2
      r
  | Result_ref r0 ->
    let Ref (l,
             f) =
      r0
    in
    if loc_comparable
         l
         Loc_null
    then k1
           f
    else k2
           r

(** val if_is_string :
    heap0
    ->
    value
    option
    ->
    (char list
    ->
    out)
    ->
    out **)

let if_is_string h o k =
  if_defined
    h
    o
    (fun v ->
    match v with
    | Value_string s ->
      k
        s
    | _ ->
      wrong
        h)

(** val if_binds_field :
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
    out **)

let if_binds_field f h l k =
  if indom_decidable0
       h
       l
       f
  then k
         (read0
           h
           l
           f)
  else wrong
         h

(** val if_binds_scope_body :
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
    out **)

let if_binds_scope_body h l k =
  if_binds_field
    Field_scope
    h
    l
    (fun v ->
    match v with
    | Value_scope s ->
      if_binds_field
        Field_body
        h
        l
        (fun v' ->
        match v' with
        | Value_body (f,
                      e) ->
          k
            s
            f
            e
        | _ ->
          wrong
            h)
    | _ ->
      wrong
        h)

(** val if_binds_field_loc :
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
    out **)

let if_binds_field_loc f h l k =
  if_binds_field
    f
    h
    l
    (fun v ->
    match v with
    | Value_loc l' ->
      k
        l'
    | _ ->
      wrong
        h)

(** val if_boolean :
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
    out **)

let if_boolean h v e1 e2 =
  match v with
  | Value_bool b ->
    if b
    then e1
           __
    else e2
           __
  | _ ->
    wrong
      h

(** val if_convert_to_bool :
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
    out **)

let if_convert_to_bool h v e1 e2 =
  if_boolean
    h
    v
    e1
    e2

(** val dont_delete_comparable :
    result
    ->
    decidable **)

let dont_delete_comparable =
  failwith "AXIOM TO BE REALIZED"

(** val if_is_loc_value :
    value
    ->
    (loc
    ->
    value
    option)
    ->
    value
    option **)

let if_is_loc_value v f =
  match v with
  | Value_loc l ->
    f
      l
  | _ ->
    None

(** val binary_op_comp_body :
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
    option **)

let binary_op_comp_body binary_op_comp0 b h v1 v2 =
  match b with
  | Binary_op_add ->
    (match v1 with
     | Value_number n1 ->
       (match v2 with
        | Value_number n2 ->
          Some
            (Value_number
            (number_add
              n1
              n2))
        | _ ->
          None)
     | Value_string s1 ->
       (match v2 with
        | Value_string s2 ->
          Some
            (Value_string
            (append0
              s1
              s2))
        | _ ->
          None)
     | _ ->
       None)
  | Binary_op_mult ->
    (match v1 with
     | Value_number n1 ->
       (match v2 with
        | Value_number n2 ->
          Some
            (Value_number
            (number_mult
              n1
              n2))
        | _ ->
          None)
     | _ ->
       None)
  | Binary_op_div ->
    (match v1 with
     | Value_number n1 ->
       (match v2 with
        | Value_number n2 ->
          Some
            (Value_number
            (number_div
              n1
              n2))
        | _ ->
          None)
     | _ ->
       None)
  | Binary_op_equal ->
    if and_decidable
         (basic_value_decidable
           v1)
         (basic_value_decidable
           v2)
    then Some
           (Value_bool
           (value_compare
             v1
             v2))
    else None
  | Binary_op_instanceof ->
    if_is_loc_value
      v1
      (fun l1 ->
      if basic_value_decidable
           v2
      then Some
             (Value_bool
             false)
      else (match v2 with
            | Value_loc l2 ->
              if indom_decidable0
                   h
                   l1
                   field_normal_prototype
              then if_is_loc_value
                     (read0
                       h
                       l1
                       field_normal_prototype)
                     (fun l3 ->
                     if indom_decidable0
                          h
                          l2
                          Field_proto
                     then if_is_loc_value
                            (read0
                              h
                              l2
                              Field_proto)
                            (fun l4 ->
                            if loc_comparable
                                 l3
                                 l4
                            then Some
                                   (Value_bool
                                   true)
                            else binary_op_comp0
                                   Binary_op_instanceof
                                   h
                                   (Value_loc
                                   l1)
                                   (Value_loc
                                   l4))
                     else None)
              else None
            | _ ->
              None))
  | Binary_op_in ->
    (match v1 with
     | Value_string f ->
       (match v2 with
        | Value_loc l ->
          Some
            (Value_bool
            (neg
              (loc_comparable
                (proto_comp
                  h
                  (Field_normal
                  f)
                  l)
                Loc_null)))
        | _ ->
          None)
     | _ ->
       None)

(** val binary_op_comp :
    binary_op
    ->
    heap0
    ->
    value
    ->
    value
    ->
    value
    option **)

let binary_op_comp x x0 x1 x2 =
  (fun bigf -> let rec f x = bigf f x in f)
    (fun f' p ->
    let (p0,
         x4) =
      p
    in
    let (p1,
         x3) =
      p0
    in
    let (x5,
         x6) =
      p1
    in
    binary_op_comp_body
      (fun x7 x8 x9 x10 ->
      f'
        (((x7,
        x8),
        x9),
        x10))
      x5
      x6
      x3
      x4)
    (((x,
    x0),
    x1),
    x2)

(** val unary_op_comp :
    unary_op
    ->
    heap0
    ->
    value
    ->
    value
    option **)

let unary_op_comp u h v =
  match u with
  | Unary_op_not ->
    (match v with
     | Value_bool b ->
       Some
         (Value_bool
         (neg
           b))
     | _ ->
       None)
  | Unary_op_void ->
    Some
      Value_undef
  | _ ->
    None

(** val typeof_comp :
    heap0
    ->
    value
    ->
    char list
    option **)

let typeof_comp h = function
| Value_undef ->
  Some
    ('u'::('n'::('d'::('e'::('f'::('i'::('n'::('e'::('d'::[])))))))))
| Value_bool b ->
  Some
    ('b'::('o'::('o'::('l'::('e'::('a'::('n'::[])))))))
| Value_number n ->
  Some
    ('n'::('u'::('m'::('b'::('e'::('r'::[]))))))
| Value_string f ->
  Some
    ('s'::('t'::('r'::('i'::('n'::('g'::[]))))))
| Value_loc l ->
  if indom_decidable0
       h
       l
       Field_body
  then Some
         ('f'::('u'::('n'::('c'::('t'::('i'::('o'::('n'::[]))))))))
  else Some
         ('o'::('b'::('j'::('e'::('c'::('t'::[]))))))
| _ ->
  None

(** val arguments_comp :
    char list
    list
    ->
    value
    list
    ->
    (field * value)
    list **)

let rec arguments_comp lx lv =
  match lx with
  | [] ->
    []
  | x :: lx' ->
    (match lv with
     | [] ->
       ((Field_normal
         x),
         Value_undef) :: (arguments_comp
                           lx'
                           [])
     | v :: lv' ->
       ((Field_normal
         x),
         v) :: (arguments_comp
                 lx'
                 lv'))

(** val run :
    int
    ->
    heap0
    ->
    scope
    ->
    expr
    ->
    out **)

let rec run max_step h0 s e =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    Out_bottom)
    (fun max_step' ->
    let run' =
      run
        max_step'
    in
    let run_list_value' =
      run_list_value
        max_step'
    in
    (match e with
     | Expr_this ->
       let l1 =
         scope_comp
           h0
           Field_this
           s
       in
       let l2 =
         proto_comp
           h0
           Field_this
           l1
       in
       if_binds_field_loc
         Field_this
         h0
         l2
         (fun l3 ->
         Out_return
         (h0,
         (Ret_result
         (Result_value
         (Value_loc
         l3)))))
     | Expr_variable name ->
       let l =
         scope_comp
           h0
           (Field_normal
           name)
           s
       in
       Out_return
       (h0,
       (ret_ref
         l
         (Field_normal
         name)))
     | Expr_literal i ->
       Out_return
         (h0,
         (Ret_result
         (Result_value
         (value_of_literal
           i))))
     | Expr_object lxe ->
       let l =
         fresh_for
           h0
       in
       let h1 =
         alloc_obj
           h0
           l
           Loc_obj_proto
       in
       let (lx,
            le0) =
         split
           lxe
       in
       run_list_value'
         h1
         s
         []
         le0
         (fun h2 lv2 ->
         let lfv =
           arguments_comp
             lx
             lv2
         in
         let h3 =
           write_fields
             h2
             l
             lfv
         in
         Out_return
         (h3,
         (Ret_result
         (Result_value
         (Value_loc
         l)))))
     | Expr_function (o,
                      f,
                      e0) ->
       (match o with
        | Some y ->
          let l =
            fresh_for
              h0
          in
          let h1 =
            alloc_obj
              h0
              l
              Loc_obj_proto
          in
          let l1 =
            fresh_for
              h1
          in
          let h2 =
            alloc_obj
              h1
              l1
              Loc_obj_proto
          in
          let l' =
            fresh_for
              h2
          in
          let h3 =
            alloc_fun
              h2
              l'
              (l1 :: s)
              f
              e0
              l
          in
          let h4 =
            write0
              h3
              l1
              (Field_normal
              y)
              (Value_loc
              l')
          in
          Out_return
          (h4,
          (Ret_result
          (Result_value
          (Value_loc
          l'))))
        | None ->
          let l =
            fresh_for
              h0
          in
          let h1 =
            alloc_obj
              h0
              l
              Loc_obj_proto
          in
          let l' =
            fresh_for
              h1
          in
          let h2 =
            alloc_fun
              h1
              l'
              s
              f
              e0
              l
          in
          Out_return
          (h2,
          (Ret_result
          (Result_value
          (Value_loc
          l')))))
     | Expr_access (e1,
                    e2) ->
       if_success
         (run'
           h0
           s
           e1)
         (fun h1 r1 ->
         if_not_eq
           Loc_null
           h1
           (getvalue_comp
             h1
             r1)
           (fun l ->
           if_success
             (run'
               h1
               s
               e2)
             (fun h2 r2 ->
             if_is_string
               h2
               (getvalue_comp
                 h2
                 r2)
               (fun f ->
               Out_return
               (h2,
               (ret_ref
                 l
                 (Field_normal
                 f)))))))
     | Expr_member (e1,
                    f) ->
       if_success
         (run'
           h0
           s
           (Expr_access
           (e1,
           (Expr_literal
           (Literal_string
           f)))))
         (fun h2 r2 ->
         if_is_ref
           h2
           r2
           (fun x f0 ->
           if_is_field_normal
             h2
             f0
             (fun x0 ->
             Out_return
             (h2,
             (Ret_result
             r2)))))
     | Expr_new (e1,
                 le2) ->
       if_success
         (run'
           h0
           s
           e1)
         (fun h1 r1 ->
         if_not_eq
           Loc_null
           h1
           (getvalue_comp
             h1
             r1)
           (fun l1 ->
           if_binds_scope_body
             h1
             l1
             (fun s3 lx e3 ->
             if_binds_field
               field_normal_prototype
               h1
               l1
               (fun v1 ->
               let l2 =
                 obj_or_glob_of_value
                   v1
               in
               run_list_value'
                 h1
                 s
                 []
                 le2
                 (fun h2 lv2 ->
                 let l4 =
                   fresh_for
                     h2
                 in
                 let h3 =
                   alloc_obj
                     h2
                     l4
                     l2
                 in
                 let l3 =
                   fresh_for
                     h3
                 in
                 let ys =
                   defs
                     lx
                     e3
                 in
                 let h4 =
                   write0
                     h3
                     l3
                     Field_proto
                     (Value_loc
                     Loc_null)
                 in
                 let h5 =
                   write0
                     h4
                     l3
                     Field_this
                     (Value_loc
                     l4)
                 in
                 let lfv =
                   arguments_comp
                     lx
                     lv2
                 in
                 let h6 =
                   write_fields
                     h5
                     l3
                     lfv
                 in
                 let h7 =
                   reserve_local_vars
                     h6
                     l3
                     ys
                 in
                 if_success_value
                   (run'
                     h7
                     (l3 :: s3)
                     e3)
                   (fun h8 v3 ->
                   let l =
                     obj_of_value
                       v3
                       l4
                   in
                   Out_return
                   (h8,
                   (Ret_result
                   (Result_value
                   (Value_loc
                   l))))))))))
     | Expr_call (e1,
                  le2) ->
       if_success
         (run'
           h0
           s
           e1)
         (fun h1 r1 ->
         if_eq
           Loc_eval
           h1
           (getvalue_comp
             h1
             r1)
           (fun _ ->
           make_error
             h0
             ('N'::('o'::('t'::('_'::('i'::('m'::('p'::('l'::('e'::('m'::('e'::('n'::('t'::('e'::('d'::[]))))))))))))))))
           (fun l1 ->
           let l2 =
             get_this
               h1
               r1
           in
           if_binds_scope_body
             h1
             l1
             (fun s3 lx e3 ->
             let ys =
               defs
                 lx
                 e3
             in
             run_list_value'
               h1
               s
               []
               le2
               (fun h2 lv2 ->
               let l3 =
                 fresh_for
                   h2
               in
               let h3 =
                 alloc_obj
                   h2
                   l3
                   Loc_null
               in
               let h4 =
                 write0
                   h3
                   l3
                   Field_this
                   (Value_loc
                   l2)
               in
               let lfv =
                 arguments_comp
                   lx
                   lv2
               in
               let h5 =
                 write_fields
                   h4
                   l3
                   lfv
               in
               let h6 =
                 write_fields
                   h5
                   l3
                   (map
                     (fun y ->
                     ((Field_normal
                     y),
                     Value_undef))
                     ys)
               in
               if_success_value
                 (run'
                   h6
                   (l3 :: s3)
                   e3)
                 (fun h7 v3 ->
                 Out_return
                 (h7,
                 (Ret_result
                 (Result_value
                 v3))))))))
     | Expr_unary_op (op,
                      e0) ->
       (match op with
        | Unary_op_not ->
          if_success_value
            (run'
              h0
              s
              e0)
            (fun h1 v1 ->
            if_defined
              h1
              (unary_op_comp
                op
                h1
                v1)
              (fun v ->
              Out_return
              (h1,
              (Ret_result
              (Result_value
              v)))))
        | Unary_op_delete ->
          if_success
            (run'
              h0
              s
              e0)
            (fun h1 r ->
            if dont_delete_comparable
                 r
            then Out_return
                   (h1,
                   (Ret_result
                   (Result_value
                   (Value_bool
                   false))))
            else let h2 =
                   dealloc
                     h1
                     r
                 in
                 Out_return
                 (h2,
                 (Ret_result
                 (Result_value
                 (Value_bool
                 true)))))
        | Unary_op_typeof ->
          if_success
            (run'
              h0
              s
              e0)
            (fun h1 r1 ->
            if_is_null_ref
              r1
              (fun x ->
              Out_return
              (h1,
              (Ret_result
              (Result_value
              (Value_string
              ('u'::('n'::('d'::('e'::('f'::('i'::('n'::('e'::('d'::[]))))))))))))))
              (fun x ->
              if_defined
                h1
                (getvalue_comp
                  h1
                  r1)
                (fun v1 ->
                if_defined
                  h1
                  (typeof_comp
                    h1
                    v1)
                  (fun str ->
                  Out_return
                  (h1,
                  (Ret_result
                  (Result_value
                  (Value_string
                  str))))))))
        | Unary_op_void ->
          if_success_value
            (run'
              h0
              s
              e0)
            (fun h1 v1 ->
            if_defined
              h1
              (unary_op_comp
                op
                h1
                v1)
              (fun v ->
              Out_return
              (h1,
              (Ret_result
              (Result_value
              v)))))
        | _ ->
          if_success
            (run'
              h0
              s
              e0)
            (fun h1 r1 ->
            if_is_ref
              h1
              r1
              (fun l f ->
              if_defined
                h1
                (getvalue_comp
                  h1
                  r1)
                (fun v ->
                if_defined
                  h1
                  (binary_op_comp
                    Binary_op_add
                    h0
                    (match op with
                     | Unary_op_pre_incr ->
                       Value_number
                         (number_of_int
                           1)
                     | Unary_op_post_incr ->
                       Value_number
                         (number_of_int
                           1)
                     | Unary_op_pre_decr ->
                       Value_number
                         (number_of_int
                           ((~-)
                           1))
                     | Unary_op_post_decr ->
                       Value_number
                         (number_of_int
                           ((~-)
                           1))
                     | _ ->
                       (raise Not_found)
                         __)
                    v)
                  (fun va ->
                  let vr =
                    match op with
                    | Unary_op_pre_incr ->
                      v
                    | Unary_op_post_incr ->
                      va
                    | Unary_op_pre_decr ->
                      v
                    | Unary_op_post_decr ->
                      va
                    | _ ->
                      (raise Not_found)
                        __
                  in
                  let h2 =
                    update
                      h1
                      l
                      f
                      va
                  in
                  Out_return
                  (h2,
                  (Ret_result
                  (Result_value
                  vr))))))))
     | Expr_binary_op (e1,
                       op,
                       e2) ->
       if_success_value
         (run'
           h0
           s
           e1)
         (fun h1 v1 ->
         if_success_value
           (run'
             h1
             s
             e2)
           (fun h2 v2 ->
           if_defined
             h2
             (binary_op_comp
               op
               h2
               v1
               v2)
             (fun v ->
             Out_return
             (h2,
             (Ret_result
             (Result_value
             v))))))
     | Expr_and (e1,
                 e2) ->
       if_success_value
         (run'
           h0
           s
           e1)
         (fun h1 v1 ->
         if_convert_to_bool
           h1
           v1
           (fun _ ->
           if_success_value
             (run'
               h1
               s
               e2)
             (fun h2 v2 ->
             Out_return
             (h2,
             (Ret_result
             (Result_value
             v2)))))
           (fun _ ->
           Out_return
           (h1,
           (Ret_result
           (Result_value
           v1)))))
     | Expr_or (e1,
                e2) ->
       if_success_value
         (run'
           h0
           s
           e1)
         (fun h1 v1 ->
         if_convert_to_bool
           h1
           v1
           (fun _ ->
           Out_return
           (h1,
           (Ret_result
           (Result_value
           v1))))
           (fun _ ->
           if_success_value
             (run'
               h1
               s
               e2)
             (fun h2 v2 ->
             Out_return
             (h2,
             (Ret_result
             (Result_value
             v2))))))
     | Expr_assign (e1,
                    o,
                    e2) ->
       (match o with
        | Some op ->
          if_success
            (run'
              h0
              s
              e1)
            (fun h1 r1 ->
            if_is_ref
              h1
              r1
              (fun l f ->
              if_defined
                h1
                (getvalue_comp
                  h1
                  r1)
                (fun v1 ->
                if_success_value
                  (run'
                    h1
                    s
                    e2)
                  (fun h2 v2 ->
                  if_defined
                    h2
                    (binary_op_comp
                      op
                      h2
                      v1
                      v2)
                    (fun v ->
                    Out_return
                    ((update
                       h2
                       l
                       f
                       v),
                    (Ret_result
                    (Result_value
                    v))))))))
        | None ->
          if_success
            (run'
              h0
              s
              e1)
            (fun h1 r1 ->
            if_is_ref
              h1
              r1
              (fun l f ->
              if_success_value
                (run'
                  h1
                  s
                  e2)
                (fun h2 v ->
                Out_return
                ((update
                   h2
                   l
                   f
                   v),
                (Ret_result
                (Result_value
                v)))))))
     | Expr_seq (e1,
                 e2) ->
       if_success
         (run'
           h0
           s
           e1)
         (fun h1 r1 ->
         if_success
           (run'
             h1
             s
             e2)
           (fun h2 r2 ->
           Out_return
           (h2,
           (Ret_result
           r2))))
     | Expr_var_decl (f,
                      o) ->
       (match o with
        | Some e0 ->
          if_success
            (run'
              h0
              s
              (Expr_assign
              ((Expr_variable
              f),
              None,
              e0)))
            (fun h1 r1 ->
            Out_return
            (h1,
            (Ret_result
            (Result_value
            Value_undef))))
        | None ->
          Out_return
            (h0,
            (Ret_result
            (Result_value
            Value_undef))))
     | Expr_if (e1,
                e2,
                eo) ->
       if_success_value
         (run'
           h0
           s
           e1)
         (fun h1 v ->
         if_boolean
           h1
           v
           (fun _ ->
           run'
             h1
             s
             e2)
           (fun _ ->
           match eo with
           | Some e3 ->
             run'
               h1
               s
               e3
           | None ->
             Out_return
               (h1,
               (Ret_result
               (Result_value
               Value_undef)))))
     | Expr_while (e1,
                   e2) ->
       if_success_value
         (run'
           h0
           s
           e1)
         (fun h1 v1 ->
         if_boolean
           h1
           v1
           (fun _ ->
           if_success
             (run'
               h1
               s
               (Expr_while
               (e1,
               e2)))
             (fun h2 r2 ->
             Out_return
             (h2,
             (Ret_result
             (Result_value
             Value_undef)))))
           (fun _ ->
           Out_return
           (h1,
           (Ret_result
           (Result_value
           Value_undef)))))
     | Expr_with (e1,
                  e2) ->
       if_success
         (run'
           h0
           s
           e1)
         (fun h1 r1 ->
         if_not_eq
           Loc_null
           h1
           (getvalue_comp
             h1
             r1)
           (fun l ->
           if_success
             (run'
               h1
               (l :: s)
               e2)
             (fun h2 r2 ->
             Out_return
             (h2,
             (Ret_result
             r2)))))
     | Expr_skip ->
       Out_return
         (h0,
         (Ret_result
         (Result_value
         Value_undef)))))
    max_step

(** val run_list_value :
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
    out **)

and run_list_value max_step h1 s lv le0 k =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    Out_bottom)
    (fun max_step' ->
    let run' =
      run
        max_step'
    in
    let run_list_value' =
      run_list_value
        max_step'
    in
    (match le0 with
     | [] ->
       k
         h1
         (rev
           lv)
     | e :: le' ->
       if_success_value
         (run'
           h1
           s
           e)
         (fun h2 v ->
         run_list_value'
           h2
           s
           (v :: lv)
           le'
           k)))
    max_step

(** val expr_undef :
    expr **)

let expr_undef =
  Expr_skip

(** val seq :
    expr
    list
    ->
    expr **)

let seq l =
  match fold_right
          (fun e s ->
          match s with
          | Some e' ->
            Some
              (Expr_seq
              (e,
              e'))
          | None ->
            Some
              e)
          None
          l with
  | Some a ->
    a
  | None ->
    expr_undef

(** val max_int :
    int **)

let max_int = max_int

(** val prog1 :
    expr **)

let prog1 =
  seq
    ((Expr_assign
    ((Expr_variable
    ('c'::('o'::('n'::('v'::('e'::('r'::('t'::[])))))))),
    None,
    (Expr_function
    (None,
    (('n'::[]) :: []),
    (Expr_call
    ((Expr_call
    ((Expr_variable
    ('n'::[])),
    ((Expr_function
    (None,
    (('n'::[]) :: []),
    (Expr_binary_op
    ((Expr_variable
    ('n'::[])),
    Binary_op_add,
    (Expr_literal
    (Literal_number
    (number_of_int
      (my_Z_of_nat
        (succ
        0))))))))) :: []))),
    ((Expr_literal
    (Literal_number
    (number_of_int
      (my_Z_of_nat
        0)))) :: []))))))) :: ((Expr_assign
    ((Expr_variable
    ('s'::('u'::('c'::('c'::[]))))),
    None,
    (Expr_function
    (None,
    (('n'::[]) :: []),
    (Expr_function
    (None,
    (('f'::[]) :: []),
    (Expr_function
    (None,
    (('x'::[]) :: []),
    (Expr_call
    ((Expr_call
    ((Expr_variable
    ('n'::[])),
    ((Expr_variable
    ('f'::[])) :: []))),
    ((Expr_call
    ((Expr_variable
    ('f'::[])),
    ((Expr_variable
    ('x'::[])) :: []))) :: []))))))))))) :: ((Expr_assign
    ((Expr_variable
    ('z'::('e'::('r'::('o'::[]))))),
    None,
    (Expr_function
    (None,
    (('f'::[]) :: []),
    (Expr_function
    (None,
    (('x'::[]) :: []),
    (Expr_variable
    ('x'::[])))))))) :: ((Expr_assign
    ((Expr_variable
    ('p'::('l'::('u'::('s'::[]))))),
    None,
    (Expr_function
    (None,
    (('x'::[]) :: (('y'::[]) :: [])),
    (Expr_call
    ((Expr_call
    ((Expr_variable
    ('x'::[])),
    ((Expr_variable
    ('s'::('u'::('c'::('c'::[]))))) :: []))),
    ((Expr_variable
    ('y'::[])) :: []))))))) :: ((Expr_var_decl
    (('o'::('n'::('e'::[]))),
    (Some
    (Expr_call
    ((Expr_variable
    ('s'::('u'::('c'::('c'::[]))))),
    ((Expr_variable
    ('z'::('e'::('r'::('o'::[]))))) :: [])))))) :: ((Expr_call
    ((Expr_variable
    ('c'::('o'::('n'::('v'::('e'::('r'::('t'::[])))))))),
    ((Expr_call
    ((Expr_variable
    ('p'::('l'::('u'::('s'::[]))))),
    ((Expr_variable
    ('o'::('n'::('e'::[])))) :: ((Expr_variable
    ('o'::('n'::('e'::[])))) :: [])))) :: []))) :: []))))))

(** val computation1 :
    out **)

let computation1 =
  run
    max_int
    init_heap
    init_scope
    prog1

(** val expr_var_decl' :
    char list
    ->
    expr
    ->
    expr **)

let expr_var_decl' s e =
  Expr_var_decl
    (s,
    (Some
    e))

(** val expr_assign' :
    expr
    ->
    expr
    ->
    expr **)

let expr_assign' e1 e2 =
  Expr_assign
    (e1,
    None,
    e2)

(** val prog2 :
    expr **)

let prog2 =
  seq
    ((expr_var_decl'
       ('i'::('d'::[]))
       (Expr_function
       (None,
       (('x'::[]) :: []),
       (Expr_variable
       ('x'::[]))))) :: ((expr_var_decl'
                           ('f'::[])
                           (Expr_function
                           (None,
                           [],
                           (seq
                             ((expr_assign'
                                (Expr_member
                                (Expr_this,
                                ('x'::[])))
                                (Expr_literal
                                (Literal_number
                                (number_of_int
                                  (my_Z_of_nat
                                    0))))) :: ((expr_assign'
                                                 (Expr_member
                                                 (Expr_this,
                                                 ('g'::[])))
                                                 (Expr_function
                                                 (None,
                                                 [],
                                                 (seq
                                                   ((expr_assign'
                                                      (Expr_member
                                                      (Expr_this,
                                                      ('x'::[])))
                                                      (Expr_literal
                                                      (Literal_number
                                                      (number_of_int
                                                        (my_Z_of_nat
                                                          (succ
                                                          0)))))) :: (Expr_this :: [])))))) :: (expr_undef :: []))))))) :: (
    (expr_var_decl'
      ('h'::[])
      (Expr_function
      (None,
      [],
      (seq
        [])))) :: ((expr_assign'
                     (Expr_member
                     ((Expr_variable
                     ('h'::[])),
                     ('p'::('r'::('o'::('t'::('o'::('t'::('y'::('p'::('e'::[])))))))))))
                     (Expr_new
                     ((Expr_variable
                     ('f'::[])),
                     []))) :: ((expr_var_decl'
                                 ('t'::('e'::('s'::('t'::[]))))
                                 (Expr_new
                                 ((Expr_variable
                                 ('h'::[])),
                                 []))) :: ((Expr_call
    ((Expr_variable
    ('i'::('d'::[]))),
    ((Expr_member
    ((Expr_call
    ((Expr_member
    ((Expr_variable
    ('t'::('e'::('s'::('t'::[]))))),
    ('g'::[]))),
    [])),
    ('x'::[]))) :: []))) :: []))))))

(** val computation2 :
    out **)

let computation2 =
  run
    max_int
    init_heap
    init_scope
    prog2

(** val prog3 :
    expr **)

let prog3 =
  seq
    ((expr_var_decl'
       ('x'::[])
       (Expr_literal
       (Literal_number
       (number_of_int
         (my_Z_of_nat
           (succ
           (succ
           (succ
           (succ
           (succ
           (succ
           (succ
           (succ
           (succ
           (succ
           (succ
           (succ
           (succ
           (succ
           (succ
           (succ
           (succ
           (succ
           (succ
           (succ
           (succ
           (succ
           (succ
           (succ
           0))))))))))))))))))))))))))))) :: ((expr_var_decl'
                                                ('f'::[])
                                                (Expr_function
                                                (None,
                                                [],
                                                (Expr_variable
                                                ('x'::[]))))) :: ((Expr_call
    ((Expr_variable
    ('f'::[])),
    [])) :: [])))

(** val computation3 :
    out **)

let computation3 =
  run
    max_int
    (write0
      init_heap
      Loc_obj_proto
      (Field_normal
      ('x'::[]))
      (Value_number
      (number_of_int
        (my_Z_of_nat
          (succ
          (succ
          (succ
          (succ
          (succ
          (succ
          (succ
          (succ
          (succ
          (succ
          (succ
          (succ
          (succ
          (succ
          (succ
          (succ
          (succ
          (succ
          (succ
          (succ
          (succ
          (succ
          (succ
          (succ
          (succ
          (succ
          (succ
          (succ
          (succ
          (succ
          (succ
          (succ
          (succ
          (succ
          (succ
          (succ
          (succ
          (succ
          (succ
          (succ
          (succ
          (succ
          0))))))))))))))))))))))))))))))))))))))))))))))
    init_scope
    prog3

