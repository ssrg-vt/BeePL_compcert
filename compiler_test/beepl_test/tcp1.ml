
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
| Pair (x0, _) -> x0

(** val snd : ('a1, 'a2) prod -> 'a2 **)

let snd = function
| Pair (_, y0) -> y0

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

  let rec add x0 y0 =
    match x0 with
    | XI p -> (match y0 with
               | XI q -> XO (add_carry p q)
               | XO q -> XI (add p q)
               | XH -> XO (succ p))
    | XO p -> (match y0 with
               | XI q -> XI (add p q)
               | XO q -> XO (add p q)
               | XH -> XI p)
    | XH -> (match y0 with
             | XI q -> XO (succ q)
             | XO q -> XI q
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x0 y0 =
    match x0 with
    | XI p ->
      (match y0 with
       | XI q -> XI (add_carry p q)
       | XO q -> XO (add_carry p q)
       | XH -> XI (succ p))
    | XO p -> (match y0 with
               | XI q -> XO (add_carry p q)
               | XO q -> XI (add p q)
               | XH -> XO (succ p))
    | XH -> (match y0 with
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
  | x1 -> x1

  (** val double_pred_mask : positive -> mask **)

  let double_pred_mask = function
  | XI p -> IsPos (XO (XO p))
  | XO p -> IsPos (XO (pred_double p))
  | XH -> IsNul

  (** val sub_mask : positive -> positive -> mask **)

  let rec sub_mask x0 y0 =
    match x0 with
    | XI p ->
      (match y0 with
       | XI q -> double_mask (sub_mask p q)
       | XO q -> succ_double_mask (sub_mask p q)
       | XH -> IsPos (XO p))
    | XO p ->
      (match y0 with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XH -> (match y0 with
             | XH -> IsNul
             | _ -> IsNeg)

  (** val sub_mask_carry : positive -> positive -> mask **)

  and sub_mask_carry x0 y0 =
    match x0 with
    | XI p ->
      (match y0 with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XO p ->
      (match y0 with
       | XI q -> double_mask (sub_mask_carry p q)
       | XO q -> succ_double_mask (sub_mask_carry p q)
       | XH -> double_pred_mask p)
    | XH -> IsNeg

  (** val mul : positive -> positive -> positive **)

  let rec mul x0 y0 =
    match x0 with
    | XI p -> add y0 (XO (mul p y0))
    | XO p -> XO (mul p y0)
    | XH -> y0

  (** val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1 **)

  let rec iter f x0 = function
  | XI n' -> f (iter f (iter f x0 n') n')
  | XO n' -> iter f (iter f x0 n') n'
  | XH -> f x0

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

  let rec compare_cont r0 x0 y0 =
    match x0 with
    | XI p -> (match y0 with
               | XI q -> compare_cont r0 p q
               | XO q -> compare_cont Gt p q
               | XH -> Gt)
    | XO p -> (match y0 with
               | XI q -> compare_cont Lt p q
               | XO q -> compare_cont r0 p q
               | XH -> Gt)
    | XH -> (match y0 with
             | XH -> r0
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
  | S x0 -> succ (of_succ_nat x0)

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

  let leb x0 y0 =
    match compare x0 y0 with
    | Gt -> False
    | _ -> True

  (** val pos_div_eucl : positive -> n -> (n, n) prod **)

  let rec pos_div_eucl a b =
    match a with
    | XI a' ->
      let Pair (q, r0) = pos_div_eucl a' b in
      let r' = succ_double r0 in
      (match leb b r' with
       | True -> Pair ((succ_double q), (sub r' b))
       | False -> Pair ((double q), r'))
    | XO a' ->
      let Pair (q, r0) = pos_div_eucl a' b in
      let r' = double r0 in
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
| Cons (x0, _) -> x0

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

  let rec pos_sub x0 y0 =
    match x0 with
    | XI p ->
      (match y0 with
       | XI q -> double (pos_sub p q)
       | XO q -> succ_double (pos_sub p q)
       | XH -> Zpos (XO p))
    | XO p ->
      (match y0 with
       | XI q -> pred_double (pos_sub p q)
       | XO q -> double (pos_sub p q)
       | XH -> Zpos (Coq_Pos.pred_double p))
    | XH -> (match y0 with
             | XI q -> Zneg (XO q)
             | XO q -> Zneg (Coq_Pos.pred_double q)
             | XH -> Z0)

  (** val add : z -> z -> z **)

  let add x0 y0 =
    match x0 with
    | Z0 -> y0
    | Zpos x' ->
      (match y0 with
       | Z0 -> x0
       | Zpos y' -> Zpos (Coq_Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y0 with
       | Z0 -> x0
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Coq_Pos.add x' y'))

  (** val opp : z -> z **)

  let opp = function
  | Z0 -> Z0
  | Zpos x1 -> Zneg x1
  | Zneg x1 -> Zpos x1

  (** val pred : z -> z **)

  let pred x0 =
    add x0 (Zneg XH)

  (** val sub : z -> z -> z **)

  let sub m n0 =
    add m (opp n0)

  (** val mul : z -> z -> z **)

  let mul x0 y0 =
    match x0 with
    | Z0 -> Z0
    | Zpos x' ->
      (match y0 with
       | Z0 -> Z0
       | Zpos y' -> Zpos (Coq_Pos.mul x' y')
       | Zneg y' -> Zneg (Coq_Pos.mul x' y'))
    | Zneg x' ->
      (match y0 with
       | Z0 -> Z0
       | Zpos y' -> Zneg (Coq_Pos.mul x' y')
       | Zneg y' -> Zpos (Coq_Pos.mul x' y'))

  (** val compare : z -> z -> comparison **)

  let compare x0 y0 =
    match x0 with
    | Z0 -> (match y0 with
             | Z0 -> Eq
             | Zpos _ -> Lt
             | Zneg _ -> Gt)
    | Zpos x' -> (match y0 with
                  | Zpos y' -> Coq_Pos.compare x' y'
                  | _ -> Gt)
    | Zneg x' -> (match y0 with
                  | Zneg y' -> compOpp (Coq_Pos.compare x' y')
                  | _ -> Lt)

  (** val leb : z -> z -> bool **)

  let leb x0 y0 =
    match compare x0 y0 with
    | Gt -> False
    | _ -> True

  (** val ltb : z -> z -> bool **)

  let ltb x0 y0 =
    match compare x0 y0 with
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

  let iter n0 f x0 =
    match n0 with
    | Zpos p -> Coq_Pos.iter f x0 p
    | _ -> x0

  (** val pos_div_eucl : positive -> z -> (z, z) prod **)

  let rec pos_div_eucl a b =
    match a with
    | XI a' ->
      let Pair (q, r0) = pos_div_eucl a' b in
      let r' = add (mul (Zpos (XO XH)) r0) (Zpos XH) in
      (match ltb r' b with
       | True -> Pair ((mul (Zpos (XO XH)) q), r')
       | False -> Pair ((add (mul (Zpos (XO XH)) q) (Zpos XH)), (sub r' b)))
    | XO a' ->
      let Pair (q, r0) = pos_div_eucl a' b in
      let r' = mul (Zpos (XO XH)) r0 in
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
         let Pair (q, r0) = pos_div_eucl a' (Zpos b') in
         (match r0 with
          | Z0 -> Pair ((opp q), Z0)
          | _ -> Pair ((opp (add q (Zpos XH))), (add b r0))))
    | Zneg a' ->
      (match b with
       | Z0 -> Pair (Z0, Z0)
       | Zpos _ ->
         let Pair (q, r0) = pos_div_eucl a' b in
         (match r0 with
          | Z0 -> Pair ((opp q), Z0)
          | _ -> Pair ((opp (add q (Zpos XH))), (sub b r0)))
       | Zneg b' -> let Pair (q, r0) = pos_div_eucl a' (Zpos b') in Pair (q, (opp r0)))

  (** val div : z -> z -> z **)

  let div a b =
    let Pair (q, _) = div_eucl a b in q

  (** val modulo : z -> z -> z **)

  let modulo a b =
    let Pair (_, r0) = div_eucl a b in r0

  (** val quotrem : z -> z -> (z, z) prod **)

  let quotrem a b =
    match a with
    | Z0 -> Pair (Z0, Z0)
    | Zpos a0 ->
      (match b with
       | Z0 -> Pair (Z0, a)
       | Zpos b0 -> let Pair (q, r0) = N.pos_div_eucl a0 (Npos b0) in Pair ((of_N q), (of_N r0))
       | Zneg b0 -> let Pair (q, r0) = N.pos_div_eucl a0 (Npos b0) in Pair ((opp (of_N q)), (of_N r0)))
    | Zneg a0 ->
      (match b with
       | Z0 -> Pair (Z0, a)
       | Zpos b0 ->
         let Pair (q, r0) = N.pos_div_eucl a0 (Npos b0) in Pair ((opp (of_N q)), (opp (of_N r0)))
       | Zneg b0 -> let Pair (q, r0) = N.pos_div_eucl a0 (Npos b0) in Pair ((of_N q), (opp (of_N r0))))

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

  let eq_dec x0 y0 =
    match x0 with
    | Z0 -> (match y0 with
             | Z0 -> Left
             | _ -> Right)
    | Zpos x1 -> (match y0 with
                  | Zpos p0 -> Coq_Pos.eq_dec x1 p0
                  | _ -> Right)
    | Zneg x1 -> (match y0 with
                  | Zneg p0 -> Coq_Pos.eq_dec x1 p0
                  | _ -> Right)
 end

(** val z_lt_dec : z -> z -> sumbool **)

let z_lt_dec x0 y0 =
  match Z.compare x0 y0 with
  | Lt -> Left
  | _ -> Right

(** val z_le_dec : z -> z -> sumbool **)

let z_le_dec x0 y0 =
  match Z.compare x0 y0 with
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
  Coq_Pos.iter (fun x0 -> XO x0) z0 n0

(** val two_power_nat : nat -> z **)

let two_power_nat n0 =
  Zpos (shift_nat n0 XH)

(** val two_power_pos : positive -> z **)

let two_power_pos x0 =
  Zpos (shift_pos x0 XH)

(** val two_p : z -> z **)

let two_p = function
| Z0 -> Zpos XH
| Zpos y0 -> two_power_pos y0
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

let zshiftin b x0 =
  match b with
  | True -> Z.succ_double x0
  | False -> Z.double x0

(** val zzero_ext : z -> z -> z **)

let zzero_ext n0 x0 =
  Z.iter n0 (fun rec0 x1 -> zshiftin (Z.odd x1) (rec0 (Z.div2 x1))) (fun _ -> Z0) x0

(** val zsign_ext : z -> z -> z **)

let zsign_ext n0 x0 =
  Z.iter (Z.pred n0) (fun rec0 x1 -> zshiftin (Z.odd x1) (rec0 (Z.div2 x1))) (fun x1 ->
    match match Z.odd x1 with
          | True -> proj_sumbool (zlt Z0 n0)
          | False -> False with
    | True -> Zneg XH
    | False -> Z0) x0

(** val z_one_bits : nat -> z -> z -> z list **)

let rec z_one_bits n0 x0 i =
  match n0 with
  | O -> Nil
  | S m ->
    (match Z.odd x0 with
     | True -> Cons (i, (z_one_bits m (Z.div2 x0) (Z.add i (Zpos XH))))
     | False -> z_one_bits m (Z.div2 x0) (Z.add i (Zpos XH)))

(** val p_is_power2 : positive -> bool **)

let rec p_is_power2 = function
| XI _ -> False
| XO q -> p_is_power2 q
| XH -> True

(** val z_is_power2 : z -> z option **)

let z_is_power2 x0 = match x0 with
| Zpos p -> (match p_is_power2 p with
             | True -> Some (Z.log2 x0)
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
    let r0 = p_mod_two_p p wordsize in (match zeq r0 Z0 with
                                        | Left -> Z0
                                        | Right -> Z.sub modulus r0)

  (** val unsigned : int -> z **)

  let unsigned =
    intval

  (** val signed : int -> z **)

  let signed n0 =
    let x0 = unsigned n0 in (match zlt x0 half_modulus with
                             | Left -> x0
                             | Right -> Z.sub x0 modulus)

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

  let eq x0 y0 =
    match zeq (unsigned x0) (unsigned y0) with
    | Left -> True
    | Right -> False

  (** val lt : int -> int -> bool **)

  let lt x0 y0 =
    match zlt (signed x0) (signed y0) with
    | Left -> True
    | Right -> False

  (** val ltu : int -> int -> bool **)

  let ltu x0 y0 =
    match zlt (unsigned x0) (unsigned y0) with
    | Left -> True
    | Right -> False

  (** val neg : int -> int **)

  let neg x0 =
    repr (Z.opp (unsigned x0))

  (** val add : int -> int -> int **)

  let add x0 y0 =
    repr (Z.add (unsigned x0) (unsigned y0))

  (** val sub : int -> int -> int **)

  let sub x0 y0 =
    repr (Z.sub (unsigned x0) (unsigned y0))

  (** val mul : int -> int -> int **)

  let mul x0 y0 =
    repr (Z.mul (unsigned x0) (unsigned y0))

  (** val divs : int -> int -> int **)

  let divs x0 y0 =
    repr (Z.quot (signed x0) (signed y0))

  (** val mods : int -> int -> int **)

  let mods x0 y0 =
    repr (Z.rem (signed x0) (signed y0))

  (** val divu : int -> int -> int **)

  let divu x0 y0 =
    repr (Z.div (unsigned x0) (unsigned y0))

  (** val modu : int -> int -> int **)

  let modu x0 y0 =
    repr (Z.modulo (unsigned x0) (unsigned y0))

  (** val coq_and : int -> int -> int **)

  let coq_and x0 y0 =
    repr (Z.coq_land (unsigned x0) (unsigned y0))

  (** val coq_or : int -> int -> int **)

  let coq_or x0 y0 =
    repr (Z.coq_lor (unsigned x0) (unsigned y0))

  (** val xor : int -> int -> int **)

  let xor x0 y0 =
    repr (Z.coq_lxor (unsigned x0) (unsigned y0))

  (** val not : int -> int **)

  let not x0 =
    xor x0 mone

  (** val shl : int -> int -> int **)

  let shl x0 y0 =
    repr (Z.shiftl (unsigned x0) (unsigned y0))

  (** val shru : int -> int -> int **)

  let shru x0 y0 =
    repr (Z.shiftr (unsigned x0) (unsigned y0))

  (** val shr : int -> int -> int **)

  let shr x0 y0 =
    repr (Z.shiftr (signed x0) (unsigned y0))

  (** val rol : int -> int -> int **)

  let rol x0 y0 =
    let n0 = Z.modulo (unsigned y0) zwordsize in
    repr (Z.coq_lor (Z.shiftl (unsigned x0) n0) (Z.shiftr (unsigned x0) (Z.sub zwordsize n0)))

  (** val ror : int -> int -> int **)

  let ror x0 y0 =
    let n0 = Z.modulo (unsigned y0) zwordsize in
    repr (Z.coq_lor (Z.shiftr (unsigned x0) n0) (Z.shiftl (unsigned x0) (Z.sub zwordsize n0)))

  (** val rolm : int -> int -> int -> int **)

  let rolm x0 a m =
    coq_and (rol x0 a) m

  (** val shrx : int -> int -> int **)

  let shrx x0 y0 =
    divs x0 (shl one y0)

  (** val mulhu : int -> int -> int **)

  let mulhu x0 y0 =
    repr (Z.div (Z.mul (unsigned x0) (unsigned y0)) modulus)

  (** val mulhs : int -> int -> int **)

  let mulhs x0 y0 =
    repr (Z.div (Z.mul (signed x0) (signed y0)) modulus)

  (** val negative : int -> int **)

  let negative x0 =
    match lt x0 zero with
    | True -> one
    | False -> zero

  (** val add_carry : int -> int -> int -> int **)

  let add_carry x0 y0 cin =
    match zlt (Z.add (Z.add (unsigned x0) (unsigned y0)) (unsigned cin)) modulus with
    | Left -> zero
    | Right -> one

  (** val add_overflow : int -> int -> int -> int **)

  let add_overflow x0 y0 cin =
    let s = Z.add (Z.add (signed x0) (signed y0)) (signed cin) in
    (match match proj_sumbool (zle min_signed s) with
           | True -> proj_sumbool (zle s max_signed)
           | False -> False with
     | True -> zero
     | False -> one)

  (** val sub_borrow : int -> int -> int -> int **)

  let sub_borrow x0 y0 bin =
    match zlt (Z.sub (Z.sub (unsigned x0) (unsigned y0)) (unsigned bin)) Z0 with
    | Left -> one
    | Right -> zero

  (** val sub_overflow : int -> int -> int -> int **)

  let sub_overflow x0 y0 bin =
    let s = Z.sub (Z.sub (signed x0) (signed y0)) (signed bin) in
    (match match proj_sumbool (zle min_signed s) with
           | True -> proj_sumbool (zle s max_signed)
           | False -> False with
     | True -> zero
     | False -> one)

  (** val shr_carry : int -> int -> int **)

  let shr_carry x0 y0 =
    match match lt x0 zero with
          | True -> negb (eq (coq_and x0 (sub (shl one y0) one)) zero)
          | False -> False with
    | True -> one
    | False -> zero

  (** val zero_ext : z -> int -> int **)

  let zero_ext n0 x0 =
    repr (zzero_ext n0 (unsigned x0))

  (** val sign_ext : z -> int -> int **)

  let sign_ext n0 x0 =
    repr (zsign_ext n0 (unsigned x0))

  (** val one_bits : int -> int list **)

  let one_bits x0 =
    map repr (z_one_bits wordsize (unsigned x0) Z0)

  (** val is_power2 : int -> int option **)

  let is_power2 x0 =
    match z_is_power2 (unsigned x0) with
    | Some i -> Some (repr i)
    | None -> None

  (** val cmp : comparison0 -> int -> int -> bool **)

  let cmp c x0 y0 =
    match c with
    | Ceq -> eq x0 y0
    | Cne -> negb (eq x0 y0)
    | Clt -> lt x0 y0
    | Cle -> negb (lt y0 x0)
    | Cgt -> lt y0 x0
    | Cge -> negb (lt x0 y0)

  (** val cmpu : comparison0 -> int -> int -> bool **)

  let cmpu c x0 y0 =
    match c with
    | Ceq -> eq x0 y0
    | Cne -> negb (eq x0 y0)
    | Clt -> ltu x0 y0
    | Cle -> negb (ltu y0 x0)
    | Cgt -> ltu y0 x0
    | Cge -> negb (ltu x0 y0)

  (** val notbool : int -> int **)

  let notbool x0 =
    match eq x0 zero with
    | True -> one
    | False -> zero

  (** val divmodu2 : int -> int -> int -> (int, int) prod option **)

  let divmodu2 nhi nlo d =
    match eq_dec d zero with
    | Left -> None
    | Right ->
      let Pair (q, r0) = Z.div_eucl (Z.add (Z.mul (unsigned nhi) modulus) (unsigned nlo)) (unsigned d)
      in
      (match zle q max_unsigned with
       | Left -> Some (Pair ((repr q), (repr r0)))
       | Right -> None)

  (** val divmods2 : int -> int -> int -> (int, int) prod option **)

  let divmods2 nhi nlo d =
    match eq_dec d zero with
    | Left -> None
    | Right ->
      let Pair (q, r0) = Z.quotrem (Z.add (Z.mul (signed nhi) modulus) (unsigned nlo)) (signed d) in
      (match match proj_sumbool (zle min_signed q) with
             | True -> proj_sumbool (zle q max_signed)
             | False -> False with
       | True -> Some (Pair ((repr q), (repr r0)))
       | False -> None)

  (** val divs_from_divu : int -> int -> int **)

  let divs_from_divu x0 y0 =
    match lt x0 zero with
    | True -> (match lt y0 zero with
               | True -> divu (neg x0) (neg y0)
               | False -> neg (divu (neg x0) y0))
    | False -> (match lt y0 zero with
                | True -> neg (divu x0 (neg y0))
                | False -> divu x0 y0)

  (** val testbit : int -> z -> bool **)

  let testbit x0 i =
    Z.testbit (unsigned x0) i

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

  let size x0 =
    zsize (unsigned x0)

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

module Wordsize_Ptrofs =
 struct
  (** val wordsize : nat **)

  let wordsize =
    match ptr64 with
    | True ->
      S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    | False ->
      S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O)))))))))))))))))))))))))))))))
 end

module Ptrofs =
 struct
  (** val wordsize : nat **)

  let wordsize =
    Wordsize_Ptrofs.wordsize

  (** val modulus : z **)

  let modulus =
    two_power_nat wordsize

  type int = z
    (* singleton inductive, whose constructor was mkint *)

  (** val coq_Z_mod_modulus : z -> z **)

  let coq_Z_mod_modulus = function
  | Z0 -> Z0
  | Zpos p -> p_mod_two_p p wordsize
  | Zneg p ->
    let r0 = p_mod_two_p p wordsize in (match zeq r0 Z0 with
                                        | Left -> Z0
                                        | Right -> Z.sub modulus r0)

  (** val repr : z -> int **)

  let repr =
    coq_Z_mod_modulus

  (** val of_ints : Int.int -> int **)

  let of_ints x0 =
    repr (Int.signed x0)
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
       | Node010 x0 -> Some x0
       | Node011 (x0, _) -> Some x0
       | Node110 (_, x0) -> Some x0
       | Node111 (_, x0, _) -> Some x0
       | _ -> None)

  (** val get : positive -> 'a1 tree -> 'a1 option **)

  let get p = function
  | Empty -> None
  | Nodes m' -> get' p m'

  (** val set0 : positive -> 'a1 -> 'a1 tree' **)

  let rec set0 p x0 =
    match p with
    | XI q -> Node001 (set0 q x0)
    | XO q -> Node100 (set0 q x0)
    | XH -> Node010 x0

  (** val set' : positive -> 'a1 -> 'a1 tree' -> 'a1 tree' **)

  let rec set' p x0 m =
    match p with
    | XI q ->
      (match m with
       | Node001 r0 -> Node001 (set' q x0 r0)
       | Node010 y0 -> Node011 (y0, (set0 q x0))
       | Node011 (y0, r0) -> Node011 (y0, (set' q x0 r0))
       | Node100 l -> Node101 (l, (set0 q x0))
       | Node101 (l, r0) -> Node101 (l, (set' q x0 r0))
       | Node110 (l, y0) -> Node111 (l, y0, (set0 q x0))
       | Node111 (l, y0, r0) -> Node111 (l, y0, (set' q x0 r0)))
    | XO q ->
      (match m with
       | Node001 r0 -> Node101 ((set0 q x0), r0)
       | Node010 y0 -> Node110 ((set0 q x0), y0)
       | Node011 (y0, r0) -> Node111 ((set0 q x0), y0, r0)
       | Node100 l -> Node100 (set' q x0 l)
       | Node101 (l, r0) -> Node101 ((set' q x0 l), r0)
       | Node110 (l, y0) -> Node110 ((set' q x0 l), y0)
       | Node111 (l, y0, r0) -> Node111 ((set' q x0 l), y0, r0))
    | XH ->
      (match m with
       | Node001 r0 -> Node011 (x0, r0)
       | Node010 _ -> Node010 x0
       | Node011 (_, r0) -> Node011 (x0, r0)
       | Node100 l -> Node110 (l, x0)
       | Node101 (l, r0) -> Node111 (l, x0, r0)
       | Node110 (l, _) -> Node110 (l, x0)
       | Node111 (l, _, r0) -> Node111 (l, x0, r0))

  (** val set : positive -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let set p x0 = function
  | Empty -> Nodes (set0 p x0)
  | Nodes m' -> Nodes (set' p x0 m')

  (** val map1' : ('a1 -> 'a2) -> 'a1 tree' -> 'a2 tree' **)

  let rec map1' f = function
  | Node001 r0 -> Node001 (map1' f r0)
  | Node010 x0 -> Node010 (f x0)
  | Node011 (x0, r0) -> Node011 ((f x0), (map1' f r0))
  | Node100 l -> Node100 (map1' f l)
  | Node101 (l, r0) -> Node101 ((map1' f l), (map1' f r0))
  | Node110 (l, x0) -> Node110 ((map1' f l), (f x0))
  | Node111 (l, x0, r0) -> Node111 ((map1' f l), (f x0), (map1' f r0))

  (** val map1 : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let map1 f = function
  | Empty -> Empty
  | Nodes m0 -> Nodes (map1' f m0)
 end

module PMap =
 struct
  type 'a t = ('a, 'a PTree.t) prod

  (** val init : 'a1 -> ('a1, 'a1 PTree.t) prod **)

  let init x0 =
    Pair (x0, PTree.empty)

  (** val get : positive -> 'a1 t -> 'a1 **)

  let get i m =
    match PTree.get i (snd m) with
    | Some x0 -> x0
    | None -> fst m

  (** val set : positive -> 'a1 -> 'a1 t -> ('a1, 'a1 PTree.tree) prod **)

  let set i x0 m =
    Pair ((fst m), (PTree.set i x0 (snd m)))

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
  | OK x0 -> g x0
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

type rettype =
| Tret of typ
| Tbool
| Tint8signed
| Tint8unsigned
| Tint16signed
| Tint16unsigned
| Tvoid

type calling_convention = { cc_vararg : z option; cc_unproto : bool; cc_structret : bool }

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

type effect_label =
| Panic
| Divergence
| Read of ident
| Write of ident
| Alloc of ident

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

(** val transBeePL_types : (type1 -> type0 res) -> type1 list -> typelist res **)

let rec transBeePL_types transBeePL_type0 = function
| Nil -> OK Tnil
| Cons (t0, ts0) ->
  bind (transBeePL_type0 t0) (fun ct ->
    bind (transBeePL_types transBeePL_type0 ts0) (fun cts -> OK (Tcons (ct, cts))))

(** val typelist_list_type : typelist -> type0 list **)

let rec typelist_list_type = function
| Tnil -> Nil
| Tcons (t0, ts0) -> Cons (t0, (typelist_list_type ts0))

(** val transBeePL_type : type1 -> type0 res **)

let rec transBeePL_type = function
| Ptype t1 ->
  (match t1 with
   | Tunit -> OK (Tint0 (I8, Unsigned, { attr_volatile = False; attr_alignas = (Some (Npos XH)) }))
   | Tint1 (sz, s, a) -> OK (Tint0 (sz, s, a))
   | Tlong1 (s, a) -> OK (Tlong0 (s, a)))
| Reftype (_, bt, a) ->
  (match bt with
   | Tunit -> OK (Tpointer (Tvoid0, a))
   | Tint1 (sz, s, a0) -> OK (Tpointer ((Tint0 (sz, s, a0)), a0))
   | Tlong1 (s, a0) -> OK (Tpointer ((Tlong0 (s, a0)), a0)))
| Ftype (ts, _, t1) ->
  bind (transBeePL_types transBeePL_type ts) (fun ats ->
    bind (transBeePL_type t1) (fun rt -> OK (Tfunction (ats, rt, { cc_vararg = (Some
      (Z.of_nat (length ts))); cc_unproto = False; cc_structret = False }))))

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

type constant =
| ConsInt of Int.int
| ConsLong of Int64.int
| ConsUnit

type gconstant =
| Gvalue of constant
| Gloc of positive
| Gspace of z

type vinfo = { vname : ident; vtype : type1 }

type linfo = { lname : ident; ltype : type1; lbitfield : bitfield }

type value =
| Vunit
| Vint0 of Int.int
| Vint64 of Int64.int
| Vloc of positive * Ptrofs.int

(** val extract_list_rvtypes : vinfo list -> (ident, type1) prod list **)

let rec extract_list_rvtypes = function
| Nil -> Nil
| Cons (x0, xs) -> Cons ((Pair (x0.vname, x0.vtype)), (extract_list_rvtypes xs))

type builtin =
| Ref
| Deref
| Massgn
| Uop of unary_operation
| Bop of binary_operation
| Run of Mem.mem

type expr =
| Var of vinfo
| Const of constant * type1
| App of ident option * expr * expr list * type1
| Prim of builtin * expr list * type1
| Bind of ident * type1 * expr * expr * type1
| Cond of expr * expr * expr * type1
| Unit of type1
| Addr of linfo * Ptrofs.int
| Hexpr of Mem.mem * expr * type1

(** val typeof_expr : expr -> type1 **)

let typeof_expr = function
| Var x0 -> x0.vtype
| Const (_, t0) -> t0
| App (_, _, _, t0) -> t0
| Prim (_, _, t0) -> t0
| Bind (_, _, _, _, t') -> t'
| Cond (_, _, _, t0) -> t0
| Unit t0 -> t0
| Addr (l, _) -> l.ltype
| Hexpr (_, _, t0) -> t0

type fun_decl = { fname : ident; args : vinfo list; lvars : vinfo list; rtype : type1; body : expr }

type glob_decl = { gname : ident; gtype : type1; gval : gconstant list }

type func = fun_decl
  (* singleton inductive, whose constructor was Fun *)

type globv = glob_decl
  (* singleton inductive, whose constructor was Glob *)

type decl =
| Fdecl of func
| Gvdecl of globv

type program0 = { bprog_defs : (positive, decl) prod list; bprog_main : positive }

(** val transBeePL_value_cvalue : value -> val0 **)

let transBeePL_value_cvalue = function
| Vunit -> Vint (Int.repr Z0)
| Vint0 i -> Vint i
| Vint64 i -> Vlong i
| Vloc (p, ofs) -> Vptr (p, ofs)

type expr0 =
| Eval of val0 * type0
| Evar of ident * type0
| Efield of expr0 * ident * type0
| Evalof of expr0 * type0
| Ederef of expr0 * type0
| Eaddrof of expr0 * type0
| Eunop of unary_operation * expr0 * type0
| Ebinop of binary_operation * expr0 * expr0 * type0
| Ecast of expr0 * type0
| Eseqand of expr0 * expr0 * type0
| Eseqor of expr0 * expr0 * type0
| Econdition of expr0 * expr0 * expr0 * type0
| Esizeof of type0 * type0
| Ealignof of type0 * type0
| Eassign of expr0 * expr0 * type0
| Eassignop of binary_operation * expr0 * expr0 * type0 * type0
| Epostincr of incr_or_decr * expr0 * type0
| Ecomma of expr0 * expr0 * type0
| Ecall of expr0 * exprlist * type0
| Ebuiltin of external_function * typelist * exprlist * type0
| Eloc of block * Ptrofs.int * bitfield * type0
| Eparen of expr0 * type0 * type0
and exprlist =
| Enil
| Econs of expr0 * exprlist

type label = ident

type statement =
| Sskip
| Sdo of expr0
| Ssequence of statement * statement
| Sifthenelse of expr0 * statement * statement
| Swhile of expr0 * statement
| Sdowhile of expr0 * statement
| Sfor of statement * expr0 * statement * statement
| Sbreak
| Scontinue
| Sreturn of expr0 option
| Sswitch of expr0 * labeled_statements
| Slabel of label * statement
| Sgoto of label
and labeled_statements =
| LSnil
| LScons of z option * statement * labeled_statements

type function0 = { fn_return : type0; fn_callconv : calling_convention;
                   fn_params : (ident, type0) prod list; fn_vars : (ident, type0) prod list;
                   fn_body : statement }

type program1 = function0 program

(** val transBeePL_expr_exprs : (expr -> expr0 res) -> expr list -> exprlist res **)

let rec transBeePL_expr_exprs transBeePL_expr_expr0 = function
| Nil -> OK Enil
| Cons (e, es0) ->
  bind (transBeePL_expr_expr0 e) (fun ce ->
    bind (transBeePL_expr_exprs transBeePL_expr_expr0 es0) (fun ces -> OK (Econs (ce, ces))))

(** val exprlist_list_expr : exprlist -> expr0 list **)

let rec exprlist_list_expr = function
| Enil -> Nil
| Econs (e1, es0) -> Cons (e1, (exprlist_list_expr es0))

(** val default_expr : expr0 **)

let default_expr =
  Eval (Vundef, Tvoid0)

(** val transBeePL_expr_expr : expr -> expr0 res **)

let rec transBeePL_expr_expr = function
| Var x0 -> bind (transBeePL_type x0.vtype) (fun xt -> OK (Evar (x0.vname, xt)))
| Const (c, t0) ->
  (match c with
   | ConsInt i -> bind (transBeePL_type t0) (fun it -> OK (Eval ((Vint i), it)))
   | ConsLong i -> bind (transBeePL_type t0) (fun it -> OK (Eval ((Vlong i), it)))
   | ConsUnit -> bind (transBeePL_type t0) (fun ut -> OK (Eval ((Vint (Int.repr Z0)), ut))))
| App (_, e0, es, t0) ->
  bind (transBeePL_expr_expr e0) (fun ce ->
    bind (transBeePL_expr_exprs transBeePL_expr_expr es) (fun ces ->
      bind (transBeePL_type t0) (fun ct -> OK (Ecall (ce, ces, ct)))))
| Prim (b, es, t0) ->
  (match b with
   | Ref ->
     bind (transBeePL_expr_exprs transBeePL_expr_expr es) (fun ces ->
       bind (transBeePL_type t0) (fun ct -> OK (Eaddrof ((hd default_expr (exprlist_list_expr ces)),
         ct))))
   | Deref ->
     bind (transBeePL_expr_exprs transBeePL_expr_expr es) (fun ces ->
       bind (transBeePL_type t0) (fun ct -> OK (Ederef ((hd default_expr (exprlist_list_expr ces)),
         ct))))
   | Massgn ->
     bind (transBeePL_expr_exprs transBeePL_expr_expr es) (fun ces ->
       bind (transBeePL_type t0) (fun ct -> OK (Eassign ((hd default_expr (exprlist_list_expr ces)),
         (hd default_expr (tl (exprlist_list_expr ces))), ct))))
   | Uop o ->
     bind (transBeePL_expr_exprs transBeePL_expr_expr es) (fun ces ->
       bind (transBeePL_type t0) (fun ct -> OK (Eunop (o, (hd default_expr (exprlist_list_expr ces)),
         ct))))
   | Bop o ->
     bind (transBeePL_expr_exprs transBeePL_expr_expr es) (fun ces ->
       bind (transBeePL_type t0) (fun ct -> OK (Ebinop (o,
         (hd default_expr (exprlist_list_expr ces)), (hd default_expr (tl (exprlist_list_expr ces))),
         ct))))
   | Run _ -> OK (Eval (Vundef, Tvoid0)))
| Bind (x0, t0, e0, e', t') ->
  bind (transBeePL_type t0) (fun ct ->
    bind (transBeePL_expr_expr e0) (fun ce ->
      bind (transBeePL_expr_expr e') (fun ce' ->
        bind (transBeePL_type t') (fun ct' -> OK (Ecomma ((Eassign ((Evar (x0, ct)), ce, ct)), ce',
          ct'))))))
| Cond (e0, e', e'', t0) ->
  bind (transBeePL_expr_expr e0) (fun ce ->
    bind (transBeePL_expr_expr e') (fun ce' ->
      bind (transBeePL_expr_expr e'') (fun ce'' ->
        bind (transBeePL_type t0) (fun ct -> OK (Econdition (ce, ce', ce'', ct))))))
| Unit t0 -> bind (transBeePL_type t0) (fun ct -> OK (Eval ((transBeePL_value_cvalue Vunit), ct)))
| Addr (l, ofs) ->
  bind (transBeePL_type l.ltype) (fun ct -> OK (Eloc (l.lname, ofs, l.lbitfield, ct)))
| Hexpr (_, _, _) -> OK (Eval (Vundef, Tvoid0))

(** val check_var_const : expr -> bool **)

let check_var_const = function
| Var _ -> True
| Const (_, _) -> True
| _ -> False

(** val transBeePL_expr_st : expr -> statement res **)

let transBeePL_expr_st = function
| Var x0 ->
  bind (transBeePL_type x0.vtype) (fun ct -> OK (Sreturn (Some (Evalof ((Evar (x0.vname, ct)), ct)))))
| Const (c, t0) ->
  bind (transBeePL_type t0) (fun ct -> OK (Sreturn (Some (Evalof
    ((match c with
      | ConsInt i -> Eval ((Vint i), ct)
      | ConsLong i -> Eval ((Vlong i), ct)
      | ConsUnit -> Eval ((Vint (Int.repr Z0)), ct)), ct)))))
| App (_, e0, es, t0) ->
  bind (transBeePL_expr_expr e0) (fun ce ->
    bind (transBeePL_expr_exprs transBeePL_expr_expr es) (fun ces ->
      bind (transBeePL_type t0) (fun ct -> OK (Sdo (Ecall (ce, ces, ct))))))
| Prim (b, es, t0) ->
  (match b with
   | Ref ->
     bind (transBeePL_expr_exprs transBeePL_expr_expr es) (fun ces ->
       bind (transBeePL_type t0) (fun ct -> OK (Sdo (Eaddrof
         ((hd default_expr (exprlist_list_expr ces)), ct)))))
   | Deref ->
     bind (transBeePL_expr_exprs transBeePL_expr_expr es) (fun ces ->
       bind (transBeePL_type t0) (fun ct -> OK (Sdo (Ederef
         ((hd default_expr (exprlist_list_expr ces)), ct)))))
   | Massgn ->
     bind (transBeePL_expr_exprs transBeePL_expr_expr es) (fun ces ->
       bind (transBeePL_type t0) (fun ct -> OK (Sdo (Eassign
         ((hd default_expr (exprlist_list_expr ces)),
         (hd default_expr (tl (exprlist_list_expr ces))), ct)))))
   | Uop o ->
     bind (transBeePL_expr_exprs transBeePL_expr_expr es) (fun ces ->
       bind (transBeePL_type t0) (fun ct -> OK (Sdo (Eunop (o,
         (hd default_expr (exprlist_list_expr ces)), ct)))))
   | Bop o ->
     bind (transBeePL_expr_exprs transBeePL_expr_expr es) (fun ces ->
       bind (transBeePL_type t0) (fun ct -> OK (Sdo (Ebinop (o,
         (hd default_expr (exprlist_list_expr ces)), (hd default_expr (tl (exprlist_list_expr ces))),
         ct)))))
   | Run _ -> OK (Sdo (Eval (Vundef, Tvoid0))))
| Bind (x0, t0, e0, e', t') ->
  (match e' with
   | Var _ ->
     bind (transBeePL_expr_expr e0) (fun ce ->
       bind (transBeePL_expr_expr e') (fun ce' ->
         bind (transBeePL_type t0) (fun ct ->
           bind (transBeePL_type t') (fun _ ->
             bind (transBeePL_type (typeof_expr e')) (fun rt -> OK (Ssequence ((Sdo (Eassign ((Evar
               (x0, ct)), ce, Tvoid0))), (Sreturn (Some (Evalof (ce', rt)))))))))))
   | Const (_, t1) ->
     bind (transBeePL_type t1) (fun ct ->
       bind (transBeePL_expr_expr e0) (fun ce ->
         bind (transBeePL_expr_expr e') (fun ce' -> OK (Ssequence ((Sdo (Eassign ((Evar (x0, ct)),
           ce, Tvoid0))), (Sreturn (Some ce')))))))
   | _ ->
     bind (transBeePL_type t0) (fun ct ->
       bind (transBeePL_expr_expr e0) (fun ce ->
         bind (transBeePL_expr_expr e') (fun ce' -> OK (Ssequence ((Sdo (Eassign ((Evar (x0, ct)),
           ce, Tvoid0))), (Sdo ce')))))))
| Cond (e0, e', e'', t') ->
  bind (transBeePL_expr_expr e0) (fun ce ->
    bind (transBeePL_expr_expr e') (fun ce' ->
      bind (transBeePL_expr_expr e'') (fun ce'' ->
        bind (transBeePL_type t') (fun ct' ->
          match match check_var_const e' with
                | True -> check_var_const e''
                | False -> False with
          | True ->
            OK (Sifthenelse (ce, (Sreturn (Some (Evalof (ce', ct')))), (Sreturn (Some (Evalof (ce'',
              ct'))))))
          | False ->
            (match check_var_const e' with
             | True -> OK (Sifthenelse (ce, (Sreturn (Some (Evalof (ce', ct')))), (Sdo ce'')))
             | False ->
               (match check_var_const e'' with
                | True -> OK (Sifthenelse (ce, (Sdo ce'), (Sreturn (Some (Evalof (ce'', ct'))))))
                | False -> OK (Sifthenelse (ce, (Sdo ce'), (Sdo ce'')))))))))
| Unit t0 ->
  bind (transBeePL_type t0) (fun ct -> OK (Sreturn (Some (Evalof ((Eval
    ((transBeePL_value_cvalue Vunit), ct)), ct)))))
| Addr (l, ofs) ->
  bind (transBeePL_type l.ltype) (fun ct -> OK (Sdo (Eloc (l.lname, ofs, l.lbitfield, ct))))
| Hexpr (_, _, _) -> OK (Sdo (Eval (Vundef, Tvoid0)))

(** val default_cc : fun_decl -> calling_convention **)

let default_cc fd =
  { cc_vararg = (Some (Z.of_nat (length fd.args))); cc_unproto = False; cc_structret = False }

(** val beePLfd_function : fun_decl -> function0 fundef res **)

let beePLfd_function fd =
  bind (transBeePL_type fd.rtype) (fun crt ->
    bind (transBeePL_types transBeePL_type (unzip2 (extract_list_rvtypes fd.args))) (fun pt ->
      bind (transBeePL_types transBeePL_type (unzip2 (extract_list_rvtypes fd.lvars))) (fun vt ->
        bind (transBeePL_expr_st fd.body) (fun fbody -> OK (Internal { fn_return = crt; fn_callconv =
          (default_cc fd); fn_params =
          (zip (unzip1 (extract_list_rvtypes fd.args)) (typelist_list_type pt)); fn_vars =
          (zip (unzip1 (extract_list_rvtypes fd.lvars)) (typelist_list_type vt)); fn_body = fbody })))))

(** val gconstant_init_data : gconstant -> init_data **)

let gconstant_init_data = function
| Gvalue c ->
  (match c with
   | ConsInt i -> Init_int32 i
   | ConsLong i -> Init_int64 i
   | ConsUnit -> Init_int32 (Int.repr Z0))
| Gloc p -> Init_addrof (p, (Ptrofs.of_ints (Int.repr Z0)))
| Gspace z0 -> Init_space z0

(** val gconstants_init_datas : gconstant list -> init_data list **)

let rec gconstants_init_datas = function
| Nil -> Nil
| Cons (g, gs0) -> Cons ((gconstant_init_data g), (gconstants_init_datas gs0))

(** val beePLgd_gd : glob_decl -> type0 globvar res **)

let beePLgd_gd gv =
  bind (transBeePL_type gv.gtype) (fun gvt -> OK { gvar_info = gvt; gvar_init =
    (gconstants_init_datas gv.gval); gvar_readonly = False; gvar_volatile = False })

(** val beePLdecl_gdef : decl -> (function0 fundef, type0) globdef res **)

let beePLdecl_gdef = function
| Fdecl f -> bind (beePLfd_function f) (fun cfd -> OK (Gfun cfd))
| Gvdecl g -> bind (beePLgd_gd g) (fun gv -> OK (Gvar gv))

(** val beePLdecls_gdefs : decl list -> (function0 fundef, type0) globdef list res **)

let rec beePLdecls_gdefs = function
| Nil -> OK Nil
| Cons (d, ds0) ->
  bind (beePLdecl_gdef d) (fun gd -> bind (beePLdecls_gdefs ds0) (fun gds -> OK (Cons (gd, gds))))

(** val beePL_compcert : program0 -> program1 res **)

let beePL_compcert m =
  bind (beePLdecls_gdefs (unzip2 m.bprog_defs)) (fun cfd -> OK { prog_defs =
    (zip (unzip1 m.bprog_defs) cfd); prog_public = Nil; prog_main = m.bprog_main; prog_types = Nil;
    prog_comp_env = PTree.empty })

(** val apply_partial : 'a1 res -> ('a1 -> 'a2 res) -> 'a2 res **)

let apply_partial x0 f =
  match x0 with
  | OK x1 -> f x1
  | Error msg -> Error msg

(** val time : string -> ('a1 -> 'a2) -> 'a1 -> 'a2 **)

let time _ f =
  f

(** val transf_beepl_program_csyntax : program0 -> program1 res **)

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

(** val x : vinfo **)

let x =
  { vname = XH; vtype = (Ptype (Tint1 (I32, Unsigned, dattr))) }

(** val y : vinfo **)

let y =
  { vname = (XO XH); vtype = (Ptype (Tint1 (I32, Unsigned, dattr))) }

(** val r : vinfo **)

let r =
  { vname = (XI XH); vtype = (Ptype (Tint1 (I32, Unsigned, dattr))) }

(** val main : positive **)

let main =
  XO (XO XH)

(** val main_body : expr **)

let main_body =
  Bind (x.vname, (Ptype (Tint1 (I32, Unsigned, dattr))), (Const ((ConsInt (Int.repr (Zpos XH))),
    (Ptype (Tint1 (I32, Unsigned, dattr))))), (Bind (y.vname, (Ptype (Tint1 (I32, Unsigned, dattr))),
    (Const ((ConsInt (Int.repr (Zpos (XO XH)))), (Ptype (Tint1 (I32, Unsigned, dattr))))), (Bind
    (r.vname, (Ptype (Tint1 (I32, Unsigned, dattr))), (Prim ((Bop Oadd), (Cons ((Var x), (Cons ((Var
    y), Nil)))), (Ptype (Tint1 (I32, Unsigned, dattr))))), (Var r), (Ptype (Tint1 (I32, Unsigned,
    dattr))))), (Ptype Tunit))), (Ptype Tunit))

(** val f_main : decl **)

let f_main =
  Fdecl { fname = main; args = Nil; lvars = (Cons (x, (Cons (y, (Cons (r, Nil)))))); rtype = (Ptype
    (Tint1 (I32, Unsigned, dattr))); body = main_body }

(** val example1 : program0 **)

let example1 =
  { bprog_defs = (Cons ((Pair (main, f_main)), Nil)); bprog_main = main }

(** val tcp1 : program1 res **)

let tcp1 =
  transf_beepl_program_csyntax example1
