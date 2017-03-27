import Data.Vect

data Ratio = MkRatio Integer Nat

sgn : (Ord a, Neg a, Num a) => a -> a
sgn a = if a < 0 then (-1)
                 else if a > 0 then 1
                 else 0

Num Ratio where
    (MkRatio n1 d1) + (MkRatio n2 d2) =
      MkRatio (n1 * cast d2 + n2 * cast d1) (d1 * d2)
    (MkRatio n1 d1) * (MkRatio n2 d2) =
      MkRatio (n1 * n2) (d1 * d2)
    fromInteger i = MkRatio i 1

Neg Ratio where
    negate (MkRatio n d) = MkRatio (negate n) d
    a - b = a + negate b
    abs (MkRatio n d) = MkRatio (abs n) d

Fractional Ratio where
    recip (MkRatio n1 d1) =
       MkRatio (sgn n1 * cast d1) (cast (abs n1))
    a / b = a * recip b

nMax : Nat -> Nat -> Nat
nMax Z m = m
nMax n Z = n
nMax (S n) (S m) = S (nMax n m)

nMaxCommutative : (n : Nat) -> (m : Nat) -> nMax n m = nMax m n
nMaxCommutative Z Z     = Refl
nMaxCommutative Z (S m) = Refl
nMaxCommutative (S n) Z = Refl
nMaxCommutative (S n) (S m) = cong (nMaxCommutative n m)

data Expr : Nat -> Type where
    EPlus  : Expr n -> Expr k -> Expr (nMax n k)
    EMinus : Expr n -> Expr k -> Expr (nMax n k)
    EMult  : Expr n -> Expr k -> Expr (nMax n k)
    EDiv   : Expr n -> Expr k -> Expr (nMax n k)
    EConst : Ratio  -> Expr 0
    EVar   : (n : Nat) -> Expr (S n)

(+) : Expr n -> Expr m -> Expr (nMax n m)
(+) = EPlus

(-) : Expr n -> Expr m -> Expr (nMax n m)
(-) = EMinus

(*) : Expr n -> Expr m -> Expr (nMax n m)
(*) = EMult

(/) : Expr n -> Expr m -> Expr (nMax n m)
(/) = EDiv

c : Ratio -> Expr 0
c = EConst

v : (n : Nat) -> Expr (S n)
v = EVar

nMaxIsAddition : (n : Nat) -> (k : Nat) -> (m ** n + m = nMax n k)
nMaxIsAddition Z Z = (_ ** Refl)
nMaxIsAddition Z (S m) = (_ ** Refl)
nMaxIsAddition (S n) Z = (0 ** rewrite plusZeroRightNeutral n in Refl)
nMaxIsAddition (S n) (S m) = let (m ** prf) = nMaxIsAddition n m in
    (_ ** rewrite sym prf in Refl)

nMaxLemma1 : Vect (nMax n k) a -> (m ** Vect (n + m) a)
nMaxLemma1 {n} {k} prf = let (x ** p) = nMaxIsAddition n k
                          in (x ** rewrite p in prf)

nMaxLemma2 : Vect (nMax n k) a -> (m ** Vect (k + m) a)
nMaxLemma2 {n} {k} prf = nMaxLemma1 {n=k} {k=n}
    (rewrite nMaxCommutative k n in prf)

natToFin' : (k : Nat) -> (n : Nat) -> {auto ok : k `LT` n} -> Fin n
natToFin' Z (S n) = FZ
natToFin' (S k) (S n) {ok} = FS (natToFin' k n {ok = fromLteSucc ok})

eval : Expr m -> Vect m Ratio -> Ratio
eval (EConst c)   _ = c
eval (EVar n)     v = natToFin' n (S n) {ok = lteRefl} `index` v
eval (EPlus  a b {n} {k}) v = let (x1 ** v1) = nMaxLemma1 v
                                  (x2 ** v2) = nMaxLemma2 v
    in eval a (take {m = x1} n v1) + eval b (take {m = x2} k v2)
eval (EMinus a b {n} {k}) v = let (x1 ** v1) = nMaxLemma1 v
                                  (x2 ** v2) = nMaxLemma2 v
    in eval a (take {m = x1} n v1) - eval b (take {m = x2} k v2)
eval (EMult  a b {n} {k}) v = let (x1 ** v1) = nMaxLemma1 v
                                  (x2 ** v2) = nMaxLemma2 v
    in eval a (take {m = x1} n v1) * eval b (take {m = x2} k v2)
eval (EDiv   a b {n} {k}) v = let (x1 ** v1) = nMaxLemma1 v
                                  (x2 ** v2) = nMaxLemma2 v
    in eval a (take {m = x1} n v1) / eval b (take {m = x2} k v2)
