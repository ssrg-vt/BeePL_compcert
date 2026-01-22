
type unit0 =
| Tt

type bool =
| True
| False

(** val negb : bool -> bool **)

let negb = function
| True -> False
| False -> True

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

(** val fst : ('a1, 'a2) prod -> 'a1 **)

let fst = function
| Pair (x, _) -> x

(** val snd : ('a1, 'a2) prod -> 'a2 **)

let snd = function
| Pair (_, y) -> y

type 'a list =
| Nil
| Cons of 'a * 'a list

(** val length : 'a1 list -> nat **)

let rec length = function
| Nil -> O
| Cons (_, l') -> S (length l')

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

type sumbool =
| Left
| Right

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos =
 struct
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
 end

module Coq_Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p -> (match y with
               | XI q -> XO (add_carry p q)
               | XO q -> XI (add p q)
               | XH -> XO (succ p))
    | XO p -> (match y with
               | XI q -> XI (add p q)
               | XO q -> XO (add p q)
               | XH -> XI p)
    | XH -> (match y with
             | XI q -> XO (succ q)
             | XO q -> XI q
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XI (add_carry p q)
       | XO q -> XO (add_carry p q)
       | XH -> XI (succ p))
    | XO p -> (match y with
               | XI q -> XO (add_carry p q)
               | XO q -> XI (add p q)
               | XH -> XO (succ p))
    | XH -> (match y with
             | XI q -> XI (succ q)
             | XO q -> XO (succ q)
             | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  (** val pred_N : positive -> n **)

  let pred_N = function
  | XI p -> Npos (XO p)
  | XO p -> Npos (pred_double p)
  | XH -> N0

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos XH
  | IsPos p -> IsPos (XI p)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p -> IsPos (XO p)
  | x0 -> x0

  (** val double_pred_mask : positive -> mask **)

  let double_pred_mask = function
  | XI p -> IsPos (XO (XO p))
  | XO p -> IsPos (XO (pred_double p))
  | XH -> IsNul

  (** val sub_mask : positive -> positive -> mask **)

  let rec sub_mask x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double_mask (sub_mask p q)
       | XO q -> succ_double_mask (sub_mask p q)
       | XH -> IsPos (XO p))
    | XO p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XH -> (match y with
             | XH -> IsNul
             | _ -> IsNeg)

  (** val sub_mask_carry : positive -> positive -> mask **)

  and sub_mask_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XO p ->
      (match y with
       | XI q -> double_mask (sub_mask_carry p q)
       | XO q -> succ_double_mask (sub_mask_carry p q)
       | XH -> double_pred_mask p)
    | XH -> IsNeg

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1 **)

  let rec iter f x = function
  | XI n' -> f (iter f (iter f x n') n')
  | XO n' -> iter f (iter f x n') n'
  | XH -> f x

  (** val div2 : positive -> positive **)

  let div2 = function
  | XI p0 -> p0
  | XO p0 -> p0
  | XH -> XH

  (** val div2_up : positive -> positive **)

  let div2_up = function
  | XI p0 -> succ p0
  | XO p0 -> p0
  | XH -> XH

  (** val size : positive -> positive **)

  let rec size = function
  | XI p0 -> succ (size p0)
  | XO p0 -> succ (size p0)
  | XH -> XH

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p -> (match y with
               | XI q -> compare_cont r p q
               | XO q -> compare_cont Gt p q
               | XH -> Gt)
    | XO p -> (match y with
               | XI q -> compare_cont Lt p q
               | XO q -> compare_cont r p q
               | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val coq_Nsucc_double : n -> n **)

  let coq_Nsucc_double = function
  | N0 -> Npos XH
  | Npos p -> Npos (XI p)

  (** val coq_Ndouble : n -> n **)

  let coq_Ndouble = function
  | N0 -> N0
  | Npos p -> Npos (XO p)

  (** val coq_lor : positive -> positive -> positive **)

  let rec coq_lor p q =
    match p with
    | XI p0 -> (match q with
                | XI q0 -> XI (coq_lor p0 q0)
                | XO q0 -> XI (coq_lor p0 q0)
                | XH -> p)
    | XO p0 -> (match q with
                | XI q0 -> XI (coq_lor p0 q0)
                | XO q0 -> XO (coq_lor p0 q0)
                | XH -> XI p0)
    | XH -> (match q with
             | XO q0 -> XI q0
             | _ -> q)

  (** val coq_land : positive -> positive -> n **)

  let rec coq_land p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Nsucc_double (coq_land p0 q0)
       | XO q0 -> coq_Ndouble (coq_land p0 q0)
       | XH -> Npos XH)
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (coq_land p0 q0)
       | XO q0 -> coq_Ndouble (coq_land p0 q0)
       | XH -> N0)
    | XH -> (match q with
             | XO _ -> N0
             | _ -> Npos XH)

  (** val ldiff : positive -> positive -> n **)

  let rec ldiff p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (ldiff p0 q0)
       | XO q0 -> coq_Nsucc_double (ldiff p0 q0)
       | XH -> Npos (XO p0))
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (ldiff p0 q0)
       | XO q0 -> coq_Ndouble (ldiff p0 q0)
       | XH -> Npos p)
    | XH -> (match q with
             | XO _ -> Npos XH
             | _ -> N0)

  (** val coq_lxor : positive -> positive -> n **)

  let rec coq_lxor p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (coq_lxor p0 q0)
       | XO q0 -> coq_Nsucc_double (coq_lxor p0 q0)
       | XH -> Npos (XO p0))
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Nsucc_double (coq_lxor p0 q0)
       | XO q0 -> coq_Ndouble (coq_lxor p0 q0)
       | XH -> Npos (XI p0))
    | XH -> (match q with
             | XI q0 -> Npos (XO q0)
             | XO q0 -> Npos (XI q0)
             | XH -> N0)

  (** val testbit : positive -> n -> bool **)

  let rec testbit p n0 =
    match p with
    | XI p0 -> (match n0 with
                | N0 -> True
                | Npos n1 -> testbit p0 (pred_N n1))
    | XO p0 -> (match n0 with
                | N0 -> False
                | Npos n1 -> testbit p0 (pred_N n1))
    | XH -> (match n0 with
             | N0 -> True
             | Npos _ -> False)

  (** val of_succ_nat : nat -> positive **)

  let rec of_succ_nat = function
  | O -> XH
  | S x -> succ (of_succ_nat x)

  (** val eq_dec : positive -> positive -> sumbool **)

  let rec eq_dec p x0 =
    match p with
    | XI p0 -> (match x0 with
                | XI p1 -> eq_dec p0 p1
                | _ -> Right)
    | XO p0 -> (match x0 with
                | XO p1 -> eq_dec p0 p1
                | _ -> Right)
    | XH -> (match x0 with
             | XH -> Left
             | _ -> Right)
 end

module N =
 struct
  (** val succ_double : n -> n **)

  let succ_double = function
  | N0 -> Npos XH
  | Npos p -> Npos (XI p)

  (** val double : n -> n **)

  let double = function
  | N0 -> N0
  | Npos p -> Npos (XO p)

  (** val succ_pos : n -> positive **)

  let succ_pos = function
  | N0 -> XH
  | Npos p -> Coq_Pos.succ p

  (** val sub : n -> n -> n **)

  let sub n0 m =
    match n0 with
    | N0 -> N0
    | Npos n' ->
      (match m with
       | N0 -> n0
       | Npos m' -> (match Coq_Pos.sub_mask n' m' with
                     | Coq_Pos.IsPos p -> Npos p
                     | _ -> N0))

  (** val compare : n -> n -> comparison **)

  let compare n0 m =
    match n0 with
    | N0 -> (match m with
             | N0 -> Eq
             | Npos _ -> Lt)
    | Npos n' -> (match m with
                  | N0 -> Gt
                  | Npos m' -> Coq_Pos.compare n' m')

  (** val leb : n -> n -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> False
    | _ -> True

  (** val pos_div_eucl : positive -> n -> (n, n) prod **)

  let rec pos_div_eucl a b =
    match a with
    | XI a' ->
      let Pair (q, r) = pos_div_eucl a' b in
      let r' = succ_double r in
      (match leb b r' with
       | True -> Pair ((succ_double q), (sub r' b))
       | False -> Pair ((double q), r'))
    | XO a' ->
      let Pair (q, r) = pos_div_eucl a' b in
      let r' = double r in
      (match leb b r' with
       | True -> Pair ((succ_double q), (sub r' b))
       | False -> Pair ((double q), r'))
    | XH ->
      (match b with
       | N0 -> Pair (N0, (Npos XH))
       | Npos p -> (match p with
                    | XH -> Pair ((Npos XH), N0)
                    | _ -> Pair (N0, (Npos XH))))

  (** val coq_lor : n -> n -> n **)

  let coq_lor n0 m =
    match n0 with
    | N0 -> m
    | Npos p -> (match m with
                 | N0 -> n0
                 | Npos q -> Npos (Coq_Pos.coq_lor p q))

  (** val coq_land : n -> n -> n **)

  let coq_land n0 m =
    match n0 with
    | N0 -> N0
    | Npos p -> (match m with
                 | N0 -> N0
                 | Npos q -> Coq_Pos.coq_land p q)

  (** val ldiff : n -> n -> n **)

  let ldiff n0 m =
    match n0 with
    | N0 -> N0
    | Npos p -> (match m with
                 | N0 -> n0
                 | Npos q -> Coq_Pos.ldiff p q)

  (** val coq_lxor : n -> n -> n **)

  let coq_lxor n0 m =
    match n0 with
    | N0 -> m
    | Npos p -> (match m with
                 | N0 -> n0
                 | Npos q -> Coq_Pos.coq_lxor p q)

  (** val testbit : n -> n -> bool **)

  let testbit a n0 =
    match a with
    | N0 -> False
    | Npos p -> Coq_Pos.testbit p n0
 end

(** val hd : 'a1 -> 'a1 list -> 'a1 **)

let hd default = function
| Nil -> default
| Cons (x, _) -> x

(** val tl : 'a1 list -> 'a1 list **)

let tl = function
| Nil -> Nil
| Cons (_, m) -> m

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| Nil -> Nil
| Cons (a, t0) -> Cons ((f a), (map f t0))

module Z =
 struct
  (** val double : z -> z **)

  let double = function
  | Z0 -> Z0
  | Zpos p -> Zpos (XO p)
  | Zneg p -> Zneg (XO p)

  (** val succ_double : z -> z **)

  let succ_double = function
  | Z0 -> Zpos XH
  | Zpos p -> Zpos (XI p)
  | Zneg p -> Zneg (Coq_Pos.pred_double p)

  (** val pred_double : z -> z **)

  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p -> Zpos (Coq_Pos.pred_double p)
  | Zneg p -> Zneg (XI p)

  (** val pos_sub : positive -> positive -> z **)

  let rec pos_sub x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double (pos_sub p q)
       | XO q -> succ_double (pos_sub p q)
       | XH -> Zpos (XO p))
    | XO p ->
      (match y with
       | XI q -> pred_double (pos_sub p q)
       | XO q -> double (pos_sub p q)
       | XH -> Zpos (Coq_Pos.pred_double p))
    | XH -> (match y with
             | XI q -> Zneg (XO q)
             | XO q -> Zneg (Coq_Pos.pred_double q)
             | XH -> Z0)

  (** val add : z -> z -> z **)

  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Coq_Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Coq_Pos.add x' y'))

  (** val opp : z -> z **)

  let opp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0

  (** val pred : z -> z **)

  let pred x =
    add x (Zneg XH)

  (** val sub : z -> z -> z **)

  let sub m n0 =
    add m (opp n0)

  (** val mul : z -> z -> z **)

  let mul x y =
    match x with
    | Z0 -> Z0
    | Zpos x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zpos (Coq_Pos.mul x' y')
       | Zneg y' -> Zneg (Coq_Pos.mul x' y'))
    | Zneg x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zneg (Coq_Pos.mul x' y')
       | Zneg y' -> Zpos (Coq_Pos.mul x' y'))

  (** val compare : z -> z -> comparison **)

  let compare x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Eq
             | Zpos _ -> Lt
             | Zneg _ -> Gt)
    | Zpos x' -> (match y with
                  | Zpos y' -> Coq_Pos.compare x' y'
                  | _ -> Gt)
    | Zneg x' -> (match y with
                  | Zneg y' -> compOpp (Coq_Pos.compare x' y')
                  | _ -> Lt)

  (** val leb : z -> z -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> False
    | _ -> True

  (** val ltb : z -> z -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> True
    | _ -> False

  (** val of_nat : nat -> z **)

  let of_nat = function
  | O -> Z0
  | S n1 -> Zpos (Coq_Pos.of_succ_nat n1)

  (** val of_N : n -> z **)

  let of_N = function
  | N0 -> Z0
  | Npos p -> Zpos p

  (** val iter : z -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

  let iter n0 f x =
    match n0 with
    | Zpos p -> Coq_Pos.iter f x p
    | _ -> x

  (** val pos_div_eucl : positive -> z -> (z, z) prod **)

  let rec pos_div_eucl a b =
    match a with
    | XI a' ->
      let Pair (q, r) = pos_div_eucl a' b in
      let r' = add (mul (Zpos (XO XH)) r) (Zpos XH) in
      (match ltb r' b with
       | True -> Pair ((mul (Zpos (XO XH)) q), r')
       | False -> Pair ((add (mul (Zpos (XO XH)) q) (Zpos XH)), (sub r' b)))
    | XO a' ->
      let Pair (q, r) = pos_div_eucl a' b in
      let r' = mul (Zpos (XO XH)) r in
      (match ltb r' b with
       | True -> Pair ((mul (Zpos (XO XH)) q), r')
       | False -> Pair ((add (mul (Zpos (XO XH)) q) (Zpos XH)), (sub r' b)))
    | XH ->
      (match leb (Zpos (XO XH)) b with
       | True -> Pair (Z0, (Zpos XH))
       | False -> Pair ((Zpos XH), Z0))

  (** val div_eucl : z -> z -> (z, z) prod **)

  let div_eucl a b =
    match a with
    | Z0 -> Pair (Z0, Z0)
    | Zpos a' ->
      (match b with
       | Z0 -> Pair (Z0, Z0)
       | Zpos _ -> pos_div_eucl a' b
       | Zneg b' ->
         let Pair (q, r) = pos_div_eucl a' (Zpos b') in
         (match r with
          | Z0 -> Pair ((opp q), Z0)
          | _ -> Pair ((opp (add q (Zpos XH))), (add b r))))
    | Zneg a' ->
      (match b with
       | Z0 -> Pair (Z0, Z0)
       | Zpos _ ->
         let Pair (q, r) = pos_div_eucl a' b in
         (match r with
          | Z0 -> Pair ((opp q), Z0)
          | _ -> Pair ((opp (add q (Zpos XH))), (sub b r)))
       | Zneg b' -> let Pair (q, r) = pos_div_eucl a' (Zpos b') in Pair (q, (opp r)))

  (** val div : z -> z -> z **)

  let div a b =
    let Pair (q, _) = div_eucl a b in q

  (** val modulo : z -> z -> z **)

  let modulo a b =
    let Pair (_, r) = div_eucl a b in r

  (** val quotrem : z -> z -> (z, z) prod **)

  let quotrem a b =
    match a with
    | Z0 -> Pair (Z0, Z0)
    | Zpos a0 ->
      (match b with
       | Z0 -> Pair (Z0, a)
       | Zpos b0 -> let Pair (q, r) = N.pos_div_eucl a0 (Npos b0) in Pair ((of_N q), (of_N r))
       | Zneg b0 -> let Pair (q, r) = N.pos_div_eucl a0 (Npos b0) in Pair ((opp (of_N q)), (of_N r)))
    | Zneg a0 ->
      (match b with
       | Z0 -> Pair (Z0, a)
       | Zpos b0 ->
         let Pair (q, r) = N.pos_div_eucl a0 (Npos b0) in Pair ((opp (of_N q)), (opp (of_N r)))
       | Zneg b0 -> let Pair (q, r) = N.pos_div_eucl a0 (Npos b0) in Pair ((of_N q), (opp (of_N r))))

  (** val quot : z -> z -> z **)

  let quot a b =
    fst (quotrem a b)

  (** val rem : z -> z -> z **)

  let rem a b =
    snd (quotrem a b)

  (** val odd : z -> bool **)

  let odd = function
  | Z0 -> False
  | Zpos p -> (match p with
               | XO _ -> False
               | _ -> True)
  | Zneg p -> (match p with
               | XO _ -> False
               | _ -> True)

  (** val div2 : z -> z **)

  let div2 = function
  | Z0 -> Z0
  | Zpos p -> (match p with
               | XH -> Z0
               | _ -> Zpos (Coq_Pos.div2 p))
  | Zneg p -> Zneg (Coq_Pos.div2_up p)

  (** val log2 : z -> z **)

  let log2 = function
  | Zpos p0 -> (match p0 with
                | XI p -> Zpos (Coq_Pos.size p)
                | XO p -> Zpos (Coq_Pos.size p)
                | XH -> Z0)
  | _ -> Z0

  (** val testbit : z -> z -> bool **)

  let testbit a = function
  | Z0 -> odd a
  | Zpos p ->
    (match a with
     | Z0 -> False
     | Zpos a0 -> Coq_Pos.testbit a0 (Npos p)
     | Zneg a0 -> negb (N.testbit (Coq_Pos.pred_N a0) (Npos p)))
  | Zneg _ -> False

  (** val shiftl : z -> z -> z **)

  let shiftl a = function
  | Z0 -> a
  | Zpos p -> Coq_Pos.iter (mul (Zpos (XO XH))) a p
  | Zneg p -> Coq_Pos.iter div2 a p

  (** val shiftr : z -> z -> z **)

  let shiftr a n0 =
    shiftl a (opp n0)

  (** val coq_lor : z -> z -> z **)

  let coq_lor a b =
    match a with
    | Z0 -> b
    | Zpos a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> Zpos (Coq_Pos.coq_lor a0 b0)
       | Zneg b0 -> Zneg (N.succ_pos (N.ldiff (Coq_Pos.pred_N b0) (Npos a0))))
    | Zneg a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> Zneg (N.succ_pos (N.ldiff (Coq_Pos.pred_N a0) (Npos b0)))
       | Zneg b0 -> Zneg (N.succ_pos (N.coq_land (Coq_Pos.pred_N a0) (Coq_Pos.pred_N b0))))

  (** val coq_land : z -> z -> z **)

  let coq_land a b =
    match a with
    | Z0 -> Z0
    | Zpos a0 ->
      (match b with
       | Z0 -> Z0
       | Zpos b0 -> of_N (Coq_Pos.coq_land a0 b0)
       | Zneg b0 -> of_N (N.ldiff (Npos a0) (Coq_Pos.pred_N b0)))
    | Zneg a0 ->
      (match b with
       | Z0 -> Z0
       | Zpos b0 -> of_N (N.ldiff (Npos b0) (Coq_Pos.pred_N a0))
       | Zneg b0 -> Zneg (N.succ_pos (N.coq_lor (Coq_Pos.pred_N a0) (Coq_Pos.pred_N b0))))

  (** val coq_lxor : z -> z -> z **)

  let coq_lxor a b =
    match a with
    | Z0 -> b
    | Zpos a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> of_N (Coq_Pos.coq_lxor a0 b0)
       | Zneg b0 -> Zneg (N.succ_pos (N.coq_lxor (Npos a0) (Coq_Pos.pred_N b0))))
    | Zneg a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> Zneg (N.succ_pos (N.coq_lxor (Coq_Pos.pred_N a0) (Npos b0)))
       | Zneg b0 -> of_N (N.coq_lxor (Coq_Pos.pred_N a0) (Coq_Pos.pred_N b0)))

  (** val eq_dec : z -> z -> sumbool **)

  let eq_dec x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Left
             | _ -> Right)
    | Zpos x0 -> (match y with
                  | Zpos p0 -> Coq_Pos.eq_dec x0 p0
                  | _ -> Right)
    | Zneg x0 -> (match y with
                  | Zneg p0 -> Coq_Pos.eq_dec x0 p0
                  | _ -> Right)
 end

(** val z_lt_dec : z -> z -> sumbool **)

let z_lt_dec x y =
  match Z.compare x y with
  | Lt -> Left
  | _ -> Right

(** val z_le_dec : z -> z -> sumbool **)

let z_le_dec x y =
  match Z.compare x y with
  | Gt -> Right
  | _ -> Left

(** val z_le_gt_dec : z -> z -> sumbool **)

let z_le_gt_dec =
  z_le_dec

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

type string =
| EmptyString
| String of ascii * string

(** val shift_nat : nat -> positive -> positive **)

let rec shift_nat n0 z0 =
  match n0 with
  | O -> z0
  | S n1 -> XO (shift_nat n1 z0)

(** val shift_pos : positive -> positive -> positive **)

let shift_pos n0 z0 =
  Coq_Pos.iter (fun x -> XO x) z0 n0

(** val two_power_nat : nat -> z **)

let two_power_nat n0 =
  Zpos (shift_nat n0 XH)

(** val two_power_pos : positive -> z **)

let two_power_pos x =
  Zpos (shift_pos x XH)

(** val two_p : z -> z **)

let two_p = function
| Z0 -> Zpos XH
| Zpos y -> two_power_pos y
| Zneg _ -> Z0

(** val zeq : z -> z -> sumbool **)

let zeq =
  Z.eq_dec

(** val zlt : z -> z -> sumbool **)

let zlt =
  z_lt_dec

(** val zle : z -> z -> sumbool **)

let zle =
  z_le_gt_dec

(** val proj_sumbool : sumbool -> bool **)

let proj_sumbool = function
| Left -> True
| Right -> False

(** val p_mod_two_p : positive -> nat -> z **)

let rec p_mod_two_p p = function
| O -> Z0
| S m ->
  (match p with
   | XI q -> Z.succ_double (p_mod_two_p q m)
   | XO q -> Z.double (p_mod_two_p q m)
   | XH -> Zpos XH)

(** val zshiftin : bool -> z -> z **)

let zshiftin b x =
  match b with
  | True -> Z.succ_double x
  | False -> Z.double x

(** val zzero_ext : z -> z -> z **)

let zzero_ext n0 x =
  Z.iter n0 (fun rec0 x0 -> zshiftin (Z.odd x0) (rec0 (Z.div2 x0))) (fun _ -> Z0) x

(** val zsign_ext : z -> z -> z **)

let zsign_ext n0 x =
  Z.iter (Z.pred n0) (fun rec0 x0 -> zshiftin (Z.odd x0) (rec0 (Z.div2 x0))) (fun x0 ->
    match match Z.odd x0 with
          | True -> proj_sumbool (zlt Z0 n0)
          | False -> False with
    | True -> Zneg XH
    | False -> Z0) x

(** val z_one_bits : nat -> z -> z -> z list **)

let rec z_one_bits n0 x i =
  match n0 with
  | O -> Nil
  | S m ->
    (match Z.odd x with
     | True -> Cons (i, (z_one_bits m (Z.div2 x) (Z.add i (Zpos XH))))
     | False -> z_one_bits m (Z.div2 x) (Z.add i (Zpos XH)))

(** val p_is_power2 : positive -> bool **)

let rec p_is_power2 = function
| XI _ -> False
| XO q -> p_is_power2 q
| XH -> True

(** val z_is_power2 : z -> z option **)

let z_is_power2 x = match x with
| Zpos p -> (match p_is_power2 p with
             | True -> Some (Z.log2 x)
             | False -> None)
| _ -> None

(** val zsize : z -> z **)

let zsize = function
| Zpos p -> Zpos (Coq_Pos.size p)
| _ -> Z0

type binary_float =
| B754_zero of bool
| B754_infinity of bool
| B754_nan of bool * positive
| B754_finite of bool * positive * z

type binary32 = binary_float

type binary64 = binary_float

(** val ptr64 : bool **)

let ptr64 =
  True

type comparison0 =
| Ceq
| Cne
| Clt
| Cle
| Cgt
| Cge

module type WORDSIZE =
 sig
  val wordsize : nat
 end

module Make =
 functor (WS:WORDSIZE) ->
 struct
  (** val wordsize : nat **)

  let wordsize =
    WS.wordsize

  (** val zwordsize : z **)

  let zwordsize =
    Z.of_nat wordsize

  (** val modulus : z **)

  let modulus =
    two_power_nat wordsize

  (** val half_modulus : z **)

  let half_modulus =
    Z.div modulus (Zpos (XO XH))

  (** val max_unsigned : z **)

  let max_unsigned =
    Z.sub modulus (Zpos XH)

  (** val max_signed : z **)

  let max_signed =
    Z.sub half_modulus (Zpos XH)

  (** val min_signed : z **)

  let min_signed =
    Z.opp half_modulus

  type int = z
    (* singleton inductive, whose constructor was mkint *)

  (** val intval : int -> z **)

  let intval i =
    i

  (** val coq_Z_mod_modulus : z -> z **)

  let coq_Z_mod_modulus = function
  | Z0 -> Z0
  | Zpos p -> p_mod_two_p p wordsize
  | Zneg p ->
    let r = p_mod_two_p p wordsize in (match zeq r Z0 with
                                       | Left -> Z0
                                       | Right -> Z.sub modulus r)

  (** val unsigned : int -> z **)

  let unsigned =
    intval

  (** val signed : int -> z **)

  let signed n0 =
    let x = unsigned n0 in (match zlt x half_modulus with
                            | Left -> x
                            | Right -> Z.sub x modulus)

  (** val repr : z -> int **)

  let repr =
    coq_Z_mod_modulus

  (** val zero : int **)

  let zero =
    repr Z0

  (** val one : int **)

  let one =
    repr (Zpos XH)

  (** val mone : int **)

  let mone =
    repr (Zneg XH)

  (** val iwordsize : int **)

  let iwordsize =
    repr zwordsize

  (** val of_bool : bool -> int **)

  let of_bool = function
  | True -> one
  | False -> zero

  (** val eq_dec : int -> int -> sumbool **)

  let eq_dec =
    zeq

  (** val eq : int -> int -> bool **)

  let eq x y =
    match zeq (unsigned x) (unsigned y) with
    | Left -> True
    | Right -> False

  (** val lt : int -> int -> bool **)

  let lt x y =
    match zlt (signed x) (signed y) with
    | Left -> True
    | Right -> False

  (** val ltu : int -> int -> bool **)

  let ltu x y =
    match zlt (unsigned x) (unsigned y) with
    | Left -> True
    | Right -> False

  (** val neg : int -> int **)

  let neg x =
    repr (Z.opp (unsigned x))

  (** val add : int -> int -> int **)

  let add x y =
    repr (Z.add (unsigned x) (unsigned y))

  (** val sub : int -> int -> int **)

  let sub x y =
    repr (Z.sub (unsigned x) (unsigned y))

  (** val mul : int -> int -> int **)

  let mul x y =
    repr (Z.mul (unsigned x) (unsigned y))

  (** val divs : int -> int -> int **)

  let divs x y =
    repr (Z.quot (signed x) (signed y))

  (** val mods : int -> int -> int **)

  let mods x y =
    repr (Z.rem (signed x) (signed y))

  (** val divu : int -> int -> int **)

  let divu x y =
    repr (Z.div (unsigned x) (unsigned y))

  (** val modu : int -> int -> int **)

  let modu x y =
    repr (Z.modulo (unsigned x) (unsigned y))

  (** val coq_and : int -> int -> int **)

  let coq_and x y =
    repr (Z.coq_land (unsigned x) (unsigned y))

  (** val coq_or : int -> int -> int **)

  let coq_or x y =
    repr (Z.coq_lor (unsigned x) (unsigned y))

  (** val xor : int -> int -> int **)

  let xor x y =
    repr (Z.coq_lxor (unsigned x) (unsigned y))

  (** val not : int -> int **)

  let not x =
    xor x mone

  (** val shl : int -> int -> int **)

  let shl x y =
    repr (Z.shiftl (unsigned x) (unsigned y))

  (** val shru : int -> int -> int **)

  let shru x y =
    repr (Z.shiftr (unsigned x) (unsigned y))

  (** val shr : int -> int -> int **)

  let shr x y =
    repr (Z.shiftr (signed x) (unsigned y))

  (** val rol : int -> int -> int **)

  let rol x y =
    let n0 = Z.modulo (unsigned y) zwordsize in
    repr (Z.coq_lor (Z.shiftl (unsigned x) n0) (Z.shiftr (unsigned x) (Z.sub zwordsize n0)))

  (** val ror : int -> int -> int **)

  let ror x y =
    let n0 = Z.modulo (unsigned y) zwordsize in
    repr (Z.coq_lor (Z.shiftr (unsigned x) n0) (Z.shiftl (unsigned x) (Z.sub zwordsize n0)))

  (** val rolm : int -> int -> int -> int **)

  let rolm x a m =
    coq_and (rol x a) m

  (** val shrx : int -> int -> int **)

  let shrx x y =
    divs x (shl one y)

  (** val mulhu : int -> int -> int **)

  let mulhu x y =
    repr (Z.div (Z.mul (unsigned x) (unsigned y)) modulus)

  (** val mulhs : int -> int -> int **)

  let mulhs x y =
    repr (Z.div (Z.mul (signed x) (signed y)) modulus)

  (** val negative : int -> int **)

  let negative x =
    match lt x zero with
    | True -> one
    | False -> zero

  (** val add_carry : int -> int -> int -> int **)

  let add_carry x y cin =
    match zlt (Z.add (Z.add (unsigned x) (unsigned y)) (unsigned cin)) modulus with
    | Left -> zero
    | Right -> one

  (** val add_overflow : int -> int -> int -> int **)

  let add_overflow x y cin =
    let s = Z.add (Z.add (signed x) (signed y)) (signed cin) in
    (match match proj_sumbool (zle min_signed s) with
           | True -> proj_sumbool (zle s max_signed)
           | False -> False with
     | True -> zero
     | False -> one)

  (** val sub_borrow : int -> int -> int -> int **)

  let sub_borrow x y bin =
    match zlt (Z.sub (Z.sub (unsigned x) (unsigned y)) (unsigned bin)) Z0 with
    | Left -> one
    | Right -> zero

  (** val sub_overflow : int -> int -> int -> int **)

  let sub_overflow x y bin =
    let s = Z.sub (Z.sub (signed x) (signed y)) (signed bin) in
    (match match proj_sumbool (zle min_signed s) with
           | True -> proj_sumbool (zle s max_signed)
           | False -> False with
     | True -> zero
     | False -> one)

  (** val shr_carry : int -> int -> int **)

  let shr_carry x y =
    match match lt x zero with
          | True -> negb (eq (coq_and x (sub (shl one y) one)) zero)
          | False -> False with
    | True -> one
    | False -> zero

  (** val zero_ext : z -> int -> int **)

  let zero_ext n0 x =
    repr (zzero_ext n0 (unsigned x))

  (** val sign_ext : z -> int -> int **)

  let sign_ext n0 x =
    repr (zsign_ext n0 (unsigned x))

  (** val one_bits : int -> int list **)

  let one_bits x =
    map repr (z_one_bits wordsize (unsigned x) Z0)

  (** val is_power2 : int -> int option **)

  let is_power2 x =
    match z_is_power2 (unsigned x) with
    | Some i -> Some (repr i)
    | None -> None

  (** val cmp : comparison0 -> int -> int -> bool **)

  let cmp c x y =
    match c with
    | Ceq -> eq x y
    | Cne -> negb (eq x y)
    | Clt -> lt x y
    | Cle -> negb (lt y x)
    | Cgt -> lt y x
    | Cge -> negb (lt x y)

  (** val cmpu : comparison0 -> int -> int -> bool **)

  let cmpu c x y =
    match c with
    | Ceq -> eq x y
    | Cne -> negb (eq x y)
    | Clt -> ltu x y
    | Cle -> negb (ltu y x)
    | Cgt -> ltu y x
    | Cge -> negb (ltu x y)

  (** val notbool : int -> int **)

  let notbool x =
    match eq x zero with
    | True -> one
    | False -> zero

  (** val divmodu2 : int -> int -> int -> (int, int) prod option **)

  let divmodu2 nhi nlo d =
    match eq_dec d zero with
    | Left -> None
    | Right ->
      let Pair (q, r) = Z.div_eucl (Z.add (Z.mul (unsigned nhi) modulus) (unsigned nlo)) (unsigned d)
      in
      (match zle q max_unsigned with
       | Left -> Some (Pair ((repr q), (repr r)))
       | Right -> None)

  (** val divmods2 : int -> int -> int -> (int, int) prod option **)

  let divmods2 nhi nlo d =
    match eq_dec d zero with
    | Left -> None
    | Right ->
      let Pair (q, r) = Z.quotrem (Z.add (Z.mul (signed nhi) modulus) (unsigned nlo)) (signed d) in
      (match match proj_sumbool (zle min_signed q) with
             | True -> proj_sumbool (zle q max_signed)
             | False -> False with
       | True -> Some (Pair ((repr q), (repr r)))
       | False -> None)

  (** val divs_from_divu : int -> int -> int **)

  let divs_from_divu x y =
    match lt x zero with
    | True -> (match lt y zero with
               | True -> divu (neg x) (neg y)
               | False -> neg (divu (neg x) y))
    | False -> (match lt y zero with
                | True -> neg (divu x (neg y))
                | False -> divu x y)

  (** val testbit : int -> z -> bool **)

  let testbit x i =
    Z.testbit (unsigned x) i

  (** val int_of_one_bits : int list -> int **)

  let rec int_of_one_bits = function
  | Nil -> zero
  | Cons (a, b) -> add (shl one a) (int_of_one_bits b)

  (** val no_overlap : int -> z -> int -> z -> bool **)

  let no_overlap ofs1 sz1 ofs2 sz2 =
    let x1 = unsigned ofs1 in
    let x2 = unsigned ofs2 in
    (match match proj_sumbool (zlt (Z.add x1 sz1) modulus) with
           | True -> proj_sumbool (zlt (Z.add x2 sz2) modulus)
           | False -> False with
     | True ->
       (match proj_sumbool (zle (Z.add x1 sz1) x2) with
        | True -> True
        | False -> proj_sumbool (zle (Z.add x2 sz2) x1))
     | False -> False)

  (** val size : int -> z **)

  let size x =
    zsize (unsigned x)

  (** val unsigned_bitfield_extract : z -> z -> int -> int **)

  let unsigned_bitfield_extract pos width n0 =
    zero_ext width (shru n0 (repr pos))

  (** val signed_bitfield_extract : z -> z -> int -> int **)

  let signed_bitfield_extract pos width n0 =
    sign_ext width (shru n0 (repr pos))

  (** val bitfield_insert : z -> z -> int -> int -> int **)

  let bitfield_insert pos width n0 p =
    let mask0 = shl (repr (Z.sub (two_p width) (Zpos XH))) (repr pos) in
    coq_or (shl (zero_ext width p) (repr pos)) (coq_and n0 (not mask0))
 end

module Wordsize_32 =
 struct
  (** val wordsize : nat **)

  let wordsize =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O)))))))))))))))))))))))))))))))
 end

module Int = Make(Wordsize_32)

module Wordsize_8 =
 struct
  (** val wordsize : nat **)

  let wordsize =
    S (S (S (S (S (S (S (S O)))))))
 end

module Byte = Make(Wordsize_8)

module Int64 =
 struct
  type int = z
    (* singleton inductive, whose constructor was mkint *)
 end

module Ptrofs =
 struct
  type int = z
    (* singleton inductive, whose constructor was mkint *)
 end

module PTree =
 struct
  type 'a tree' =
  | Node001 of 'a tree'
  | Node010 of 'a
  | Node011 of 'a * 'a tree'
  | Node100 of 'a tree'
  | Node101 of 'a tree' * 'a tree'
  | Node110 of 'a tree' * 'a
  | Node111 of 'a tree' * 'a * 'a tree'

  type 'a tree =
  | Empty
  | Nodes of 'a tree'

  type 'a t = 'a tree

  (** val empty : 'a1 t **)

  let empty =
    Empty

  (** val get' : positive -> 'a1 tree' -> 'a1 option **)

  let rec get' p m =
    match p with
    | XI q ->
      (match m with
       | Node001 m' -> get' q m'
       | Node011 (_, m') -> get' q m'
       | Node101 (_, m') -> get' q m'
       | Node111 (_, _, m') -> get' q m'
       | _ -> None)
    | XO q ->
      (match m with
       | Node100 m' -> get' q m'
       | Node101 (m', _) -> get' q m'
       | Node110 (m', _) -> get' q m'
       | Node111 (m', _, _) -> get' q m'
       | _ -> None)
    | XH ->
      (match m with
       | Node010 x -> Some x
       | Node011 (x, _) -> Some x
       | Node110 (_, x) -> Some x
       | Node111 (_, x, _) -> Some x
       | _ -> None)

  (** val get : positive -> 'a1 tree -> 'a1 option **)

  let get p = function
  | Empty -> None
  | Nodes m' -> get' p m'

  (** val set0 : positive -> 'a1 -> 'a1 tree' **)

  let rec set0 p x =
    match p with
    | XI q -> Node001 (set0 q x)
    | XO q -> Node100 (set0 q x)
    | XH -> Node010 x

  (** val set' : positive -> 'a1 -> 'a1 tree' -> 'a1 tree' **)

  let rec set' p x m =
    match p with
    | XI q ->
      (match m with
       | Node001 r -> Node001 (set' q x r)
       | Node010 y -> Node011 (y, (set0 q x))
       | Node011 (y, r) -> Node011 (y, (set' q x r))
       | Node100 l -> Node101 (l, (set0 q x))
       | Node101 (l, r) -> Node101 (l, (set' q x r))
       | Node110 (l, y) -> Node111 (l, y, (set0 q x))
       | Node111 (l, y, r) -> Node111 (l, y, (set' q x r)))
    | XO q ->
      (match m with
       | Node001 r -> Node101 ((set0 q x), r)
       | Node010 y -> Node110 ((set0 q x), y)
       | Node011 (y, r) -> Node111 ((set0 q x), y, r)
       | Node100 l -> Node100 (set' q x l)
       | Node101 (l, r) -> Node101 ((set' q x l), r)
       | Node110 (l, y) -> Node110 ((set' q x l), y)
       | Node111 (l, y, r) -> Node111 ((set' q x l), y, r))
    | XH ->
      (match m with
       | Node001 r -> Node011 (x, r)
       | Node010 _ -> Node010 x
       | Node011 (_, r) -> Node011 (x, r)
       | Node100 l -> Node110 (l, x)
       | Node101 (l, r) -> Node111 (l, x, r)
       | Node110 (l, _) -> Node110 (l, x)
       | Node111 (l, _, r) -> Node111 (l, x, r))

  (** val set : positive -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let set p x = function
  | Empty -> Nodes (set0 p x)
  | Nodes m' -> Nodes (set' p x m')

  (** val map1' : ('a1 -> 'a2) -> 'a1 tree' -> 'a2 tree' **)

  let rec map1' f = function
  | Node001 r -> Node001 (map1' f r)
  | Node010 x -> Node010 (f x)
  | Node011 (x, r) -> Node011 ((f x), (map1' f r))
  | Node100 l -> Node100 (map1' f l)
  | Node101 (l, r) -> Node101 ((map1' f l), (map1' f r))
  | Node110 (l, x) -> Node110 ((map1' f l), (f x))
  | Node111 (l, x, r) -> Node111 ((map1' f l), (f x), (map1' f r))

  (** val map1 : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let map1 f = function
  | Empty -> Empty
  | Nodes m0 -> Nodes (map1' f m0)
 end

module PMap =
 struct
  type 'a t = ('a, 'a PTree.t) prod

  (** val init : 'a1 -> ('a1, 'a1 PTree.t) prod **)

  let init x =
    Pair (x, PTree.empty)

  (** val get : positive -> 'a1 t -> 'a1 **)

  let get i m =
    match PTree.get i (snd m) with
    | Some x -> x
    | None -> fst m

  (** val set : positive -> 'a1 -> 'a1 t -> ('a1, 'a1 PTree.tree) prod **)

  let set i x m =
    Pair ((fst m), (PTree.set i x (snd m)))

  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let map f m =
    Pair ((f (fst m)), (PTree.map1 f (snd m)))
 end

module type INDEXED_TYPE =
 sig
  type t

  val index : t -> positive

  val eq : t -> t -> sumbool
 end

module IMap =
 functor (X:INDEXED_TYPE) ->
 struct
  type elt = X.t

  (** val elt_eq : X.t -> X.t -> sumbool **)

  let elt_eq =
    X.eq

  type 'x t = 'x PMap.t

  (** val init : 'a1 -> ('a1, 'a1 PTree.t) prod **)

  let init =
    PMap.init

  (** val get : X.t -> 'a1 t -> 'a1 **)

  let get i m =
    PMap.get (X.index i) m

  (** val set : X.t -> 'a1 -> 'a1 t -> ('a1, 'a1 PTree.tree) prod **)

  let set i v m =
    PMap.set (X.index i) v m

  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let map =
    PMap.map
 end

module ZIndexed =
 struct
  type t = z

  (** val index : z -> positive **)

  let index = function
  | Z0 -> XH
  | Zpos p -> XO p
  | Zneg p -> XI p

  (** val eq : z -> z -> sumbool **)

  let eq =
    zeq
 end

module ZMap = IMap(ZIndexed)

type errcode =
| MSG of string
| CTX of positive
| POS of positive

type errmsg = errcode list

type 'a res =
| OK of 'a
| Error of errmsg

(** val bind : 'a1 res -> ('a1 -> 'a2 res) -> 'a2 res **)

let bind f g =
  match f with
  | OK x -> g x
  | Error msg -> Error msg

type float = binary64

type float32 = binary32

type ident = positive

type typ =
| Tint
| Tfloat
| Tlong
| Tsingle
| Tany32
| Tany64

(** val tptr : typ **)

let tptr =
  match ptr64 with
  | True -> Tlong
  | False -> Tint

type rettype =
| Tret of typ
| Tbool
| Tint8signed
| Tint8unsigned
| Tint16signed
| Tint16unsigned
| Tvoid

type calling_convention = { cc_vararg : z option; cc_unproto : bool; cc_structret : bool }

(** val cc_default : calling_convention **)

let cc_default =
  { cc_vararg = None; cc_unproto = False; cc_structret = False }

type signature = { sig_args : typ list; sig_res : rettype; sig_cc : calling_convention }

type memory_chunk =
| Mbool
| Mint8signed
| Mint8unsigned
| Mint16signed
| Mint16unsigned
| Mint32
| Mint64
| Mfloat32
| Mfloat64
| Many32
| Many64

type init_data =
| Init_int8 of Int.int
| Init_int16 of Int.int
| Init_int32 of Int.int
| Init_int64 of Int64.int
| Init_float32 of float32
| Init_float64 of float
| Init_space of z
| Init_addrof of ident * Ptrofs.int

type 'v globvar = { gvar_info : 'v; gvar_init : init_data list; gvar_readonly : bool;
                    gvar_volatile : bool }

type ('f, 'v) globdef =
| Gfun of 'f
| Gvar of 'v globvar

type external_function =
| EF_external of string * signature
| EF_builtin of string * signature
| EF_runtime of string * signature
| EF_vload of memory_chunk
| EF_vstore of memory_chunk
| EF_malloc
| EF_free
| EF_memcpy of z * z
| EF_annot of positive * string * typ list
| EF_annot_val of positive * string * typ
| EF_inline_asm of string * signature * string list
| EF_debug of positive * ident * typ list

type signedness =
| Signed
| Unsigned

type intsize =
| I8
| I16
| I32
| IBool

type floatsize =
| F32
| F64

type attr = { attr_volatile : bool; attr_alignas : n option }

type type0 =
| Tvoid0
| Tint0 of intsize * signedness * attr
| Tlong0 of signedness * attr
| Tfloat0 of floatsize * attr
| Tpointer of type0 * attr
| Tarray of type0 * z * attr
| Tfunction of typelist * type0 * calling_convention
| Tstruct of ident * attr
| Tunion of ident * attr
and typelist =
| Tnil
| Tcons of type0 * typelist

type struct_or_union =
| Struct
| Union

type member =
| Member_plain of ident * type0
| Member_bitfield of ident * intsize * signedness * attr * z * bool

type members = member list

type composite_definition =
| Composite of ident * struct_or_union * members * attr

type composite = { co_su : struct_or_union; co_members : members; co_attr : attr; co_sizeof : 
                   z; co_alignof : z; co_rank : nat }

type composite_env = composite PTree.t

type bitfield =
| Full
| Bits of intsize * signedness * z * z

(** val typ_of_type : type0 -> typ **)

let typ_of_type = function
| Tvoid0 -> Tint
| Tint0 (_, _, _) -> Tint
| Tlong0 (_, _) -> Tlong
| Tfloat0 (f, _) -> (match f with
                     | F32 -> Tsingle
                     | F64 -> Tfloat)
| _ -> tptr

(** val rettype_of_type : type0 -> rettype **)

let rettype_of_type = function
| Tint0 (i, s, _) ->
  (match i with
   | I8 -> (match s with
            | Signed -> Tint8signed
            | Unsigned -> Tint8unsigned)
   | I16 -> (match s with
             | Signed -> Tint16signed
             | Unsigned -> Tint16unsigned)
   | I32 -> Tret Tint
   | IBool -> Tbool)
| Tlong0 (_, _) -> Tret Tlong
| Tfloat0 (f, _) -> (match f with
                     | F32 -> Tret Tsingle
                     | F64 -> Tret Tfloat)
| Tpointer (_, _) -> Tret tptr
| _ -> Tvoid

type 'f fundef =
| Internal of 'f
| External of external_function * typelist * type0 * calling_convention

type 'f program = { prog_defs : (ident, ('f fundef, type0) globdef) prod list;
                    prog_public : ident list; prog_main : ident;
                    prog_types : composite_definition list; prog_comp_env : composite_env }

type block = positive

type val0 =
| Vundef
| Vint of Int.int
| Vlong of Int64.int
| Vfloat of float
| Vsingle of float32
| Vptr of block * Ptrofs.int

type quantity =
| Q32
| Q64

type memval =
| Undef
| Byte of Byte.int
| Fragment of val0 * quantity * nat

type permission =
| Freeable
| Writable
| Readable
| Nonempty

type perm_kind =
| Max
| Cur

module Mem =
 struct
  type mem' = { mem_contents : memval ZMap.t PMap.t;
                mem_access : (z -> perm_kind -> permission option) PMap.t; nextblock : block }

  type mem = mem'
 end

type unary_operation =
| Onotbool
| Onotint
| Oneg
| Oabsfloat

type binary_operation =
| Oadd
| Osub
| Omul
| Odiv
| Omod
| Oand
| Oor
| Oxor
| Oshl
| Oshr
| Oeq
| One
| Olt
| Ogt
| Ole
| Oge

type incr_or_decr =
| Incr
| Decr

type expr =
| Eval of val0 * type0
| Evar of ident * type0
| Efield of expr * ident * type0
| Evalof of expr * type0
| Ederef of expr * type0
| Eaddrof of expr * type0
| Eunop of unary_operation * expr * type0
| Ebinop of binary_operation * expr * expr * type0
| Ecast of expr * type0
| Eseqand of expr * expr * type0
| Eseqor of expr * expr * type0
| Econdition of expr * expr * expr * type0
| Esizeof of type0 * type0
| Ealignof of type0 * type0
| Eassign of expr * expr * type0
| Eassignop of binary_operation * expr * expr * type0 * type0
| Epostincr of incr_or_decr * expr * type0
| Ecomma of expr * expr * type0
| Ecall of expr * exprlist * type0
| Ebuiltin of external_function * typelist * exprlist * type0
| Eloc of block * Ptrofs.int * bitfield * type0
| Eparen of expr * type0 * type0
and exprlist =
| Enil
| Econs of expr * exprlist

type label = ident

type statement =
| Sskip
| Sdo of expr
| Ssequence of statement * statement
| Sifthenelse of expr * statement * statement
| Swhile of expr * statement
| Sdowhile of expr * statement
| Sfor of statement * expr * statement * statement
| Sbreak
| Scontinue
| Sreturn of expr option
| Sswitch of expr * labeled_statements
| Slabel of label * statement
| Sgoto of label
and labeled_statements =
| LSnil
| LScons of z option * statement * labeled_statements

type function0 = { fn_return : type0; fn_callconv : calling_convention;
                   fn_params : (ident, type0) prod list; fn_vars : (ident, type0) prod list;
                   fn_body : statement }

type fundef0 = function0 fundef

type program0 = function0 program

type generator = { gen_next : ident; gen_trail : (ident, type0) prod list }

type 'a result =
| Err of errmsg
| Res of 'a * generator

type 'a mon = generator -> 'a result

(** val ret : 'a1 -> 'a1 mon **)

let ret x g =
  Res (x, g)

(** val bind0 : 'a1 mon -> ('a1 -> 'a2 mon) -> 'a2 mon **)

let bind0 x f g =
  match x g with
  | Err msg -> Err msg
  | Res (a, g') -> f a g'

(** val first_unused_ident : unit0 -> ident **)

let first_unused_ident =
  failwith "AXIOM TO BE REALIZED"

(** val initial_generator : unit0 -> generator **)

let initial_generator x =
  { gen_next = (first_unused_ident x); gen_trail = Nil }

(** val gensym : type0 -> ident mon **)

let gensym ty g =
  Res (g.gen_next, { gen_next = (Coq_Pos.succ g.gen_next); gen_trail = (Cons ((Pair (g.gen_next,
    ty)), g.gen_trail)) })

(** val map0 : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map0 f = function
| Nil -> Nil
| Cons (x, s') -> Cons ((f x), (map0 f s'))

type effect_label =
| Panic
| Divergence
| Read of ident
| Write of ident
| Alloc of ident
| Hstate of ident

type effect = effect_label list

type primitive_type =
| Tunit
| Tint1 of intsize * signedness * attr
| Tlong1 of signedness * attr

type basic_type = primitive_type
  (* singleton inductive, whose constructor was Bprim *)

type type1 =
| Ptype of primitive_type
| Reftype of ident * basic_type * attr
| Ftype of type1 list * effect * type1

(** val from_typelist : typelist -> type0 list **)

let rec from_typelist = function
| Tnil -> Nil
| Tcons (t0, ts0) -> Cons (t0, (from_typelist ts0))

(** val transBeePL_types : (type1 -> type0 mon) -> type1 list -> typelist mon **)

let rec transBeePL_types transBeePL_type0 = function
| Nil -> ret Tnil
| Cons (t0, ts0) ->
  bind0 (transBeePL_type0 t0) (fun ct ->
    bind0 (transBeePL_types transBeePL_type0 ts0) (fun cts -> ret (Tcons (ct, cts))))

(** val transBeePL_type : type1 -> type0 mon **)

let rec transBeePL_type = function
| Ptype t1 ->
  (match t1 with
   | Tunit -> ret Tvoid0
   | Tint1 (sz, s, a) -> ret (Tint0 (sz, s, a))
   | Tlong1 (s, a) -> ret (Tlong0 (s, a)))
| Reftype (_, bt, a) ->
  (match bt with
   | Tunit -> ret (Tpointer (Tvoid0, a))
   | Tint1 (sz, s, a') -> ret (Tpointer ((Tint0 (sz, s, a')), a))
   | Tlong1 (s, a') -> ret (Tpointer ((Tlong0 (s, a')), a)))
| Ftype (ts, _, t1) ->
  bind0 (transBeePL_types transBeePL_type ts) (fun ats ->
    bind0 (transBeePL_type t1) (fun rt ->
      ret (Tfunction (ats, rt, { cc_vararg = (Some (Z.of_nat (length ts))); cc_unproto = False;
        cc_structret = False }))))

(** val unzip1 : ('a1, 'a2) prod list -> 'a1 list **)

let rec unzip1 = function
| Nil -> Nil
| Cons (e, es0) -> Cons ((fst e), (unzip1 es0))

(** val unzip2 : ('a1, 'a2) prod list -> 'a2 list **)

let rec unzip2 = function
| Nil -> Nil
| Cons (e, es0) -> Cons ((snd e), (unzip2 es0))

(** val zip : 'a1 list -> 'a2 list -> ('a1, 'a2) prod list **)

let rec zip es1 es2 =
  match es1 with
  | Nil -> Nil
  | Cons (e1, es3) ->
    (match es2 with
     | Nil -> Nil
     | Cons (e2, es4) -> Cons ((Pair (e1, e2)), (zip es3 es4)))

type constant =
| ConsInt of Int.int
| ConsLong of Int64.int
| ConsUnit

type linfo = { lname : ident; lbitfield : bitfield }

type value =
| Vunit
| Vint0 of Int.int
| Vint64 of Int64.int
| Vloc of positive * Ptrofs.int

type builtin =
| Ref
| Deref
| Massgn
| Uop of unary_operation
| Bop of binary_operation
| Run of Mem.mem

type bsignature = { bsig_args : type1 list; bsig_ef : effect; bsig_res : type1;
                    bsig_cc : calling_convention }

(** val bsig_to_csig : bsignature -> signature mon **)

let bsig_to_csig bsig =
  bind0 (transBeePL_types transBeePL_type bsig.bsig_args) (fun cts ->
    bind0 (transBeePL_type bsig.bsig_res) (fun ct ->
      ret { sig_args = (map0 typ_of_type (from_typelist cts)); sig_res = (rettype_of_type ct);
        sig_cc = bsig.bsig_cc }))

type external_function0 =
| EF_external0 of string * bsignature

(** val befuntion_to_cefunction : external_function0 -> external_function mon **)

let befuntion_to_cefunction = function
| EF_external0 (n0, bsig) -> bind0 (bsig_to_csig bsig) (fun aef -> ret (EF_external (n0, aef)))

type expr0 =
| Val of value * type1
| Var of ident * type1
| Const of constant * type1
| App of expr0 * expr0 list * type1
| Prim of builtin * expr0 list * type1
| Bind of ident * type1 * expr0 * expr0 * type1
| Cond of expr0 * expr0 * expr0 * type1
| Unit of type1
| Addr of linfo * Ptrofs.int * type1
| Hexpr of Mem.mem * expr0 * type1
| Eapp of external_function0 * type1 list * expr0 list * type1

(** val typeof_expr : expr0 -> type1 **)

let typeof_expr = function
| Val (_, t0) -> t0
| Var (_, t0) -> t0
| Const (_, t0) -> t0
| App (_, _, t0) -> t0
| Prim (_, _, t0) -> t0
| Bind (_, _, _, _, t') -> t'
| Cond (_, _, _, t0) -> t0
| Unit t0 -> t0
| Addr (_, _, t0) -> t0
| Hexpr (_, _, t0) -> t0
| Eapp (_, _, _, t0) -> t0

type function1 = { fn_return0 : type1; fn_effect : effect; fn_callconv0 : calling_convention;
                   fn_args : (ident, type1) prod list; fn_vars0 : (ident, type1) prod list;
                   fn_body0 : expr0 }

type fundef1 =
| Internal0 of function1
| External0 of external_function0 * type1 list * type1 * calling_convention

type 'v globvar0 = 'v globvar

type ('f, 'v) globdef0 = ('f, 'v) globdef

type program1 = { prog_defs0 : (ident, (fundef1, type1) globdef0) prod list;
                  prog_public0 : ident list; prog_main0 : ident;
                  prog_types0 : composite_definition list; prog_comp_env0 : composite_env }

(** val transBeePL_value_cvalue : value -> val0 **)

let transBeePL_value_cvalue = function
| Vunit -> Vint (Int.repr Z0)
| Vint0 i -> Vint i
| Vint64 i -> Vlong i
| Vloc (p, ofs) -> Vptr (p, ofs)

(** val transBeePL_expr_exprs : (expr0 -> expr mon) -> expr0 list -> exprlist mon **)

let rec transBeePL_expr_exprs transBeePL_expr_expr0 = function
| Nil -> ret Enil
| Cons (e, es0) ->
  bind0 (transBeePL_expr_expr0 e) (fun ce ->
    bind0 (transBeePL_expr_exprs transBeePL_expr_expr0 es0) (fun ces -> ret (Econs (ce, ces))))

(** val exprlist_list_expr : exprlist -> expr list **)

let rec exprlist_list_expr = function
| Enil -> Nil
| Econs (e1, es0) -> Cons (e1, (exprlist_list_expr es0))

(** val default_expr : expr **)

let default_expr =
  Eval (Vundef, Tvoid0)

(** val transBeePL_expr_expr : expr0 -> expr mon **)

let rec transBeePL_expr_expr = function
| Val (v, t0) -> bind0 (transBeePL_type t0) (fun vt -> ret (Eval ((transBeePL_value_cvalue v), vt)))
| Var (x, t0) -> bind0 (transBeePL_type t0) (fun xt -> ret (Evar (x, xt)))
| Const (c, t0) ->
  (match c with
   | ConsInt i -> bind0 (transBeePL_type t0) (fun it -> ret (Eval ((Vint i), it)))
   | ConsLong i -> bind0 (transBeePL_type t0) (fun it -> ret (Eval ((Vlong i), it)))
   | ConsUnit -> bind0 (transBeePL_type t0) (fun ut -> ret (Eval ((Vint (Int.repr Z0)), ut))))
| App (e0, es, t0) ->
  bind0 (transBeePL_expr_expr e0) (fun ce ->
    bind0 (transBeePL_expr_exprs transBeePL_expr_expr es) (fun ces ->
      bind0 (transBeePL_type t0) (fun ct -> ret (Ecall (ce, ces, ct)))))
| Prim (b, es, t0) ->
  (match b with
   | Ref ->
     bind0 (transBeePL_expr_exprs transBeePL_expr_expr es) (fun ces ->
       bind0 (transBeePL_type t0) (fun ct ->
         bind0 (gensym ct) (fun tv ->
           ret (Ecomma ((Eassign ((Evar (tv, ct)), (hd default_expr (exprlist_list_expr ces)), ct)),
             (Eaddrof ((Evar (tv, ct)), ct)), ct)))))
   | Deref ->
     bind0 (transBeePL_expr_exprs transBeePL_expr_expr es) (fun ces ->
       bind0 (transBeePL_type t0) (fun ct ->
         ret (Evalof ((hd default_expr (exprlist_list_expr ces)), ct))))
   | Massgn ->
     bind0 (transBeePL_expr_exprs transBeePL_expr_expr es) (fun ces ->
       bind0 (transBeePL_type t0) (fun ct ->
         ret (Eassign ((hd default_expr (exprlist_list_expr ces)),
           (hd default_expr (tl (exprlist_list_expr ces))), ct))))
   | Uop o ->
     bind0 (transBeePL_expr_exprs transBeePL_expr_expr es) (fun ces ->
       bind0 (transBeePL_type t0) (fun ct ->
         ret (Eunop (o, (hd default_expr (exprlist_list_expr ces)), ct))))
   | Bop o ->
     bind0 (transBeePL_expr_exprs transBeePL_expr_expr es) (fun ces ->
       bind0 (transBeePL_type t0) (fun ct ->
         ret (Ebinop (o, (hd default_expr (exprlist_list_expr ces)),
           (hd default_expr (tl (exprlist_list_expr ces))), ct))))
   | Run _ -> ret (Eval (Vundef, Tvoid0)))
| Bind (x, t0, e0, e', t') ->
  bind0 (transBeePL_type t0) (fun ct ->
    bind0 (transBeePL_expr_expr e0) (fun ce ->
      bind0 (transBeePL_expr_expr e') (fun ce' ->
        bind0 (transBeePL_type t') (fun ct' ->
          ret (Ecomma ((Eassign ((Evar (x, ct)), ce, ct)), ce', ct'))))))
| Cond (e0, e', e'', t0) ->
  bind0 (transBeePL_expr_expr e0) (fun ce ->
    bind0 (transBeePL_expr_expr e') (fun ce' ->
      bind0 (transBeePL_expr_expr e'') (fun ce'' ->
        bind0 (transBeePL_type t0) (fun ct -> ret (Econdition (ce, ce', ce'', ct))))))
| Unit t0 -> bind0 (transBeePL_type t0) (fun ct -> ret (Eval ((transBeePL_value_cvalue Vunit), ct)))
| Addr (l, ofs, t0) ->
  bind0 (transBeePL_type t0) (fun ct -> ret (Eloc (l.lname, ofs, l.lbitfield, ct)))
| Hexpr (_, _, _) -> ret (Eval (Vundef, Tvoid0))
| Eapp (ef, ts, es, t0) ->
  bind0 (befuntion_to_cefunction ef) (fun cef ->
    bind0 (transBeePL_types transBeePL_type ts) (fun cts ->
      bind0 (transBeePL_type t0) (fun ct ->
        bind0 (transBeePL_expr_exprs transBeePL_expr_expr es) (fun ces ->
          ret (Ebuiltin (cef, cts, ces, ct))))))

(** val check_var_const : expr0 -> bool **)

let check_var_const = function
| Var (_, _) -> True
| Const (_, _) -> True
| _ -> False

(** val transBeePL_expr_st : expr0 -> statement mon **)

let transBeePL_expr_st = function
| Val (v, t0) ->
  bind0 (transBeePL_type t0) (fun vt -> ret (Sreturn (Some (Eval ((transBeePL_value_cvalue v), vt)))))
| Var (x, t0) ->
  bind0 (transBeePL_type t0) (fun ct -> ret (Sreturn (Some (Evalof ((Evar (x, ct)), ct)))))
| Const (c, t0) ->
  bind0 (transBeePL_type t0) (fun ct ->
    ret (Sreturn (Some (Evalof
      ((match c with
        | ConsInt i -> Eval ((Vint i), ct)
        | ConsLong i -> Eval ((Vlong i), ct)
        | ConsUnit -> Eval ((Vint (Int.repr Z0)), ct)), ct)))))
| App (e0, es, t0) ->
  bind0 (transBeePL_expr_expr e0) (fun ce ->
    bind0 (transBeePL_expr_exprs transBeePL_expr_expr es) (fun ces ->
      bind0 (transBeePL_type t0) (fun ct -> ret (Sdo (Ecall (ce, ces, ct))))))
| Prim (b, es, t0) ->
  (match b with
   | Ref ->
     bind0 (transBeePL_expr_exprs transBeePL_expr_expr es) (fun ces ->
       bind0 (transBeePL_type t0) (fun ct ->
         bind0 (gensym ct) (fun tv ->
           ret (Sdo (Ecomma ((Eassign ((Evar (tv, ct)), (hd default_expr (exprlist_list_expr ces)),
             ct)), (Eaddrof ((Evar (tv, ct)), ct)), ct))))))
   | Deref ->
     bind0 (transBeePL_expr_exprs transBeePL_expr_expr es) (fun ces ->
       bind0 (transBeePL_type t0) (fun ct ->
         ret (Sdo (Evalof ((hd default_expr (exprlist_list_expr ces)), ct)))))
   | Massgn ->
     bind0 (transBeePL_expr_exprs transBeePL_expr_expr es) (fun ces ->
       bind0 (transBeePL_type t0) (fun ct ->
         ret (Sdo (Eassign ((hd default_expr (exprlist_list_expr ces)),
           (hd default_expr (tl (exprlist_list_expr ces))), ct)))))
   | Uop o ->
     bind0 (transBeePL_expr_exprs transBeePL_expr_expr es) (fun ces ->
       bind0 (transBeePL_type t0) (fun ct ->
         ret (Sdo (Eunop (o, (hd default_expr (exprlist_list_expr ces)), ct)))))
   | Bop o ->
     bind0 (transBeePL_expr_exprs transBeePL_expr_expr es) (fun ces ->
       bind0 (transBeePL_type t0) (fun ct ->
         ret (Sdo (Ebinop (o, (hd default_expr (exprlist_list_expr ces)),
           (hd default_expr (tl (exprlist_list_expr ces))), ct)))))
   | Run _ -> ret (Sdo (Eval (Vundef, Tvoid0))))
| Bind (x, t0, e0, e', _) ->
  (match e' with
   | Var (_, t') ->
     bind0 (transBeePL_expr_expr e0) (fun ce ->
       bind0 (transBeePL_expr_expr e') (fun ce' ->
         bind0 (transBeePL_type t0) (fun ct ->
           bind0 (transBeePL_type t') (fun _ ->
             bind0 (transBeePL_type (typeof_expr e')) (fun rt ->
               ret (Ssequence ((Sdo (Eassign ((Evar (x, ct)), ce, Tvoid0))), (Sreturn (Some (Evalof
                 (ce', rt)))))))))))
   | Const (_, t1) ->
     bind0 (transBeePL_type t1) (fun ct ->
       bind0 (transBeePL_expr_expr e0) (fun ce ->
         bind0 (transBeePL_expr_expr e') (fun ce' ->
           ret (Ssequence ((Sdo (Eassign ((Evar (x, ct)), ce, Tvoid0))), (Sreturn (Some ce')))))))
   | _ ->
     bind0 (transBeePL_type t0) (fun ct ->
       bind0 (transBeePL_expr_expr e0) (fun ce ->
         bind0 (transBeePL_expr_expr e') (fun ce' ->
           ret (Ssequence ((Sdo (Eassign ((Evar (x, ct)), ce, Tvoid0))), (Sdo ce')))))))
| Cond (e0, e', e'', t') ->
  bind0 (transBeePL_expr_expr e0) (fun ce ->
    bind0 (transBeePL_expr_expr e') (fun ce' ->
      bind0 (transBeePL_expr_expr e'') (fun ce'' ->
        bind0 (transBeePL_type t') (fun ct' ->
          match match check_var_const e' with
                | True -> check_var_const e''
                | False -> False with
          | True ->
            ret (Sifthenelse (ce, (Sreturn (Some (Evalof (ce', ct')))), (Sreturn (Some (Evalof (ce'',
              ct'))))))
          | False ->
            (match check_var_const e' with
             | True -> ret (Sifthenelse (ce, (Sreturn (Some (Evalof (ce', ct')))), (Sdo ce'')))
             | False ->
               (match check_var_const e'' with
                | True -> ret (Sifthenelse (ce, (Sdo ce'), (Sreturn (Some (Evalof (ce'', ct'))))))
                | False -> ret (Sifthenelse (ce, (Sdo ce'), (Sdo ce'')))))))))
| Unit t0 ->
  bind0 (transBeePL_type t0) (fun ct ->
    ret (Sreturn (Some (Evalof ((Eval ((transBeePL_value_cvalue Vunit), ct)), ct)))))
| Addr (l, ofs, t0) ->
  bind0 (transBeePL_type t0) (fun ct -> ret (Sdo (Eloc (l.lname, ofs, l.lbitfield, ct))))
| Hexpr (_, _, _) -> ret (Sdo (Eval (Vundef, Tvoid0)))
| Eapp (ef, ts, es, t0) ->
  bind0 (befuntion_to_cefunction ef) (fun cef ->
    bind0 (transBeePL_types transBeePL_type ts) (fun cts ->
      bind0 (transBeePL_type t0) (fun ct ->
        bind0 (transBeePL_expr_exprs transBeePL_expr_expr es) (fun ces ->
          ret (Sdo (Ebuiltin (cef, cts, ces, ct)))))))

(** val transBeePL_function_function : function1 -> function0 res **)

let transBeePL_function_function fd =
  match transBeePL_type fd.fn_return0 (initial_generator Tt) with
  | Err msg -> Error msg
  | Res (crt, _) ->
    (match transBeePL_types transBeePL_type (unzip2 fd.fn_args) (initial_generator Tt) with
     | Err msg -> Error msg
     | Res (pt, _) ->
       (match transBeePL_types transBeePL_type (unzip2 fd.fn_vars0) (initial_generator Tt) with
        | Err msg -> Error msg
        | Res (vt, _) ->
          (match transBeePL_expr_st fd.fn_body0 (initial_generator Tt) with
           | Err msg -> Error msg
           | Res (fbody, _) ->
             OK { fn_return = crt; fn_callconv = cc_default; fn_params =
               (zip (unzip1 fd.fn_args) (from_typelist pt)); fn_vars =
               (zip (unzip1 fd.fn_vars0) (from_typelist vt)); fn_body = fbody })))

(** val transBeePL_fundef_fundef : fundef1 -> fundef0 res **)

let transBeePL_fundef_fundef = function
| Internal0 f -> bind (transBeePL_function_function f) (fun tf -> OK (Internal tf))
| External0 (ef, ts, t0, cc) ->
  (match befuntion_to_cefunction ef (initial_generator Tt) with
   | Err msg -> Error msg
   | Res (cef, _) ->
     (match transBeePL_types transBeePL_type ts (initial_generator Tt) with
      | Err msg -> Error msg
      | Res (cts, _) ->
        (match transBeePL_type t0 (initial_generator Tt) with
         | Err msg -> Error msg
         | Res (ct, _) -> OK (External (cef, cts, ct, cc)))))

(** val transBeePLglobvar_globvar : type1 globvar0 -> type0 globvar res **)

let transBeePLglobvar_globvar gv =
  match transBeePL_type gv.gvar_info (initial_generator Tt) with
  | Err msg -> Error msg
  | Res (gvt, _) ->
    OK { gvar_info = gvt; gvar_init = gv.gvar_init; gvar_readonly = gv.gvar_readonly; gvar_volatile =
      gv.gvar_volatile }

(** val transBeePL_globdef_globdef : (fundef1, type1) globdef0 -> (fundef0, type0) globdef res **)

let transBeePL_globdef_globdef = function
| Gfun f -> bind (transBeePL_fundef_fundef f) (fun cf -> OK (Gfun cf))
| Gvar g -> bind (transBeePLglobvar_globvar g) (fun cg -> OK (Gvar cg))

(** val transBeePL_globdefs_globdefs :
    (fundef1, type1) globdef0 list -> (fundef0, type0) globdef list res **)

let rec transBeePL_globdefs_globdefs = function
| Nil -> OK Nil
| Cons (d, ds) ->
  bind (transBeePL_globdef_globdef d) (fun gd ->
    bind (transBeePL_globdefs_globdefs ds) (fun gds0 -> OK (Cons (gd, gds0))))

(** val beePL_compcert : program1 -> program0 res **)

let beePL_compcert p =
  bind (transBeePL_globdefs_globdefs (unzip2 p.prog_defs0)) (fun pds -> OK { prog_defs =
    (zip (unzip1 p.prog_defs0) pds); prog_public = p.prog_public0; prog_main = p.prog_main0;
    prog_types = p.prog_types0; prog_comp_env = p.prog_comp_env0 })

(** val apply_partial : 'a1 res -> ('a1 -> 'a2 res) -> 'a2 res **)

let apply_partial x f =
  match x with
  | OK x1 -> f x1
  | Error msg -> Error msg

(** val time : string -> ('a1 -> 'a2) -> 'a1 -> 'a2 **)

let time _ f =
  f

(** val transf_beepl_program_csyntax : program1 -> program0 res **)

let transf_beepl_program_csyntax p =
  apply_partial (OK p)
    (time (String ((Ascii (True, True, False, False, False, False, True, False)), (String ((Ascii
      (True, True, False, False, True, True, True, False)), (String ((Ascii (True, False, False,
      True, True, True, True, False)), (String ((Ascii (False, True, True, True, False, True, True,
      False)), (String ((Ascii (False, False, True, False, True, True, True, False)), (String ((Ascii
      (True, False, False, False, False, True, True, False)), (String ((Ascii (False, False, False,
      True, True, True, True, False)), (String ((Ascii (False, False, False, False, False, True,
      False, False)), (String ((Ascii (True, True, True, False, False, True, True, False)), (String
      ((Ascii (True, False, True, False, False, True, True, False)), (String ((Ascii (False, True,
      True, True, False, True, True, False)), (String ((Ascii (True, False, True, False, False, True,
      True, False)), (String ((Ascii (False, True, False, False, True, True, True, False)), (String
      ((Ascii (True, False, False, False, False, True, True, False)), (String ((Ascii (False, False,
      True, False, True, True, True, False)), (String ((Ascii (True, False, False, True, False, True,
      True, False)), (String ((Ascii (True, True, True, True, False, True, True, False)), (String
      ((Ascii (False, True, True, True, False, True, True, False)),
      EmptyString)))))))))))))))))))))))))))))))))))) beePL_compcert)

(** val dattr : attr **)

let dattr =
  { attr_volatile = False; attr_alignas = (Some (Npos (XO (XO XH)))) }

(** val _x : positive **)

let _x =
  XH

(** val _y : positive **)

let _y =
  XO XH

(** val _r : positive **)

let _r =
  XI XH

(** val _main : ident **)

let _main =
  XO (XI (XI (XO (XI (XO (XO (XI (XO (XI (XO (XO (XO (XI (XO (XO (XI (XO (XI (XI (XI (XO (XI (XO
    XH)))))))))))))))))))))))

(** val f_main : function1 **)

let f_main =
  { fn_return0 = (Ptype (Tint1 (I32, Unsigned, dattr))); fn_effect = Nil; fn_callconv0 = cc_default;
    fn_args = Nil; fn_vars0 = (Cons ((Pair (_x, (Ptype (Tint1 (I32, Unsigned, dattr))))), (Cons
    ((Pair (_y, (Ptype (Tint1 (I32, Unsigned, dattr))))), (Cons ((Pair (_r, (Ptype (Tint1 (I32,
    Unsigned, dattr))))), Nil)))))); fn_body0 = (Bind (_x, (Ptype (Tint1 (I32, Unsigned, dattr))),
    (Const ((ConsInt (Int.repr (Zpos XH))), (Ptype (Tint1 (I32, Unsigned, dattr))))), (Bind (_y,
    (Ptype (Tint1 (I32, Unsigned, dattr))), (Const ((ConsInt (Int.repr (Zpos (XO XH)))), (Ptype
    (Tint1 (I32, Unsigned, dattr))))), (Bind (_r, (Ptype (Tint1 (I32, Unsigned, dattr))), (Prim ((Bop
    Oadd), (Cons ((Var (_x, (Ptype (Tint1 (I32, Unsigned, dattr))))), (Cons ((Var (_y, (Ptype (Tint1
    (I32, Unsigned, dattr))))), Nil)))), (Ptype (Tint1 (I32, Unsigned, dattr))))), (Var (_r, (Ptype
    (Tint1 (I32, Unsigned, dattr))))), (Ptype (Tint1 (I32, Unsigned, dattr))))), (Ptype Tunit))),
    (Ptype Tunit))) }

(** val composites : composite_definition list **)

let composites =
  Nil

(** val global_definitions : (ident, (fundef1, type1) globdef0) prod list **)

let global_definitions =
  Cons ((Pair (_main, (Gfun (Internal0 f_main)))), Nil)

(** val public_idents : ident list **)

let public_idents =
  Cons (_main, Nil)

(** val example1 : program1 **)

let example1 =
  { prog_defs0 = global_definitions; prog_public0 = public_idents; prog_main0 = _main; prog_types0 =
    composites; prog_comp_env0 = PTree.empty }

(** val tcp1 : program0 res **)

let tcp1 =
  transf_beepl_program_csyntax example1
