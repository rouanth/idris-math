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

nFold : (t -> a -> a) -> a -> Vect n t -> a
nFold f a [] = a
nFold f a (x :: xs) = f x (nFold f a xs)

data Expr : Nat -> Type where
    EPlus  : Expr n -> Expr k -> Expr (nMax n k)
    EMinus : Expr n -> Expr k -> Expr (nMax n k)
    EMult  : Expr n -> Expr k -> Expr (nMax n k)
    EDiv   : Expr n -> Expr k -> Expr (nMax n k)
    EConst : Ratio  -> Expr 0
    EVar   : (n : Nat) -> Expr (S n)
    ESubExp: Expr n -> (p : Vect n (k ** Expr k)) ->
                 Expr ((nFold Main.nMax Z . map DPair.fst) p)

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

evalSubExpLemma : (k : Nat) -> (z : Expr k) ->
    (ps : Vect n (o : Nat ** Expr o)) ->
    (m ** k + m = (nFold Main.nMax 0 . map DPair.fst) ((k ** z) :: ps))
evalSubExpLemma k z ps =
    let (m ** pf) = nMaxIsAddition k ((nFold nMax 0 . map DPair.fst) ps)
     in (m ** rewrite pf in Refl)

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
eval (ESubExp b p {n}) v = let params = map (g . f n p v) (range {len = n})
                            in eval b params
  where f : (n : Nat) ->
            (p : Vect n (k ** Expr k)) ->
            Vect ((nFold Main.nMax Z . map DPair.fst) p) Ratio ->
            Fin n ->
            (k ** m ** (Expr k, Vect (k + m) Ratio))
        f Z _ _ _ impossible
        f (S n) ((k ** z) :: ps) xs FS = let (m ** pf) = evalSubExpLemma k z ps
            in (k ** m ** rewrite pf in (z, xs))
        f (S n) ((kn ** zn) :: ps) xs (FS b) =
            let (i ** s) = nMaxLemma2 xs
                nxs = Vect.take (((nFold nMax Z . map DPair.fst) ps)) {m = i} s
            in f n ps nxs b
        g : (k ** m ** (Expr k, Vect (k + m) Ratio)) -> Ratio
        g (k ** _ ** (z, xs)) = eval z (take k xs)

evalFn : (m : Nat) -> Type
evalFn Z = Ratio
evalFn (S n) = Ratio -> evalFn n

minusSuccNSucc : (n : Nat) -> (m : Nat) ->
    {auto ok1 : (m `LT` n)} ->
    {auto ok2 : (m `LTE` n)} -> n - m = S (n - S m)
minusSuccNSucc Z _ {ok1} = void (succNotLTEzero ok1)
minusSuccNSucc (S n) Z = rewrite minusSuccOne n in Refl
minusSuccNSucc (S n) (S m) {ok1} {ok2} = minusSuccNSucc n m
    {ok1 = fromLteSucc ok1} {ok2 = fromLteSucc ok2}

eval' : (e : Expr m) -> evalFn m
eval' e {m} = evalIn' m (rewrite sym (minusZeroN m) in []) {ok=lteRefl}
    where evalIn' : (a : Nat) -> {auto ok : a `LTE` m} -> Vect (m-a) Ratio ->
                    evalFn a
          evalIn' Z v = eval e (rewrite sym (minusZeroRight m) in v)
          evalIn' (S a) v {ok} = \n => evalIn' a (rewrite minusSuccNSucc
              {ok2 = lteSuccLeft ok} m a in (n :: v)) {ok = lteSuccLeft ok}
