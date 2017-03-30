import Data.Vect

%default total

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

toVect : List a -> (n ** Vect n a)
toVect [] = (_ ** [])
toVect (x :: xs) = let (n ** v) = toVect xs
                    in (S n ** x :: v)

data Expr : Nat -> Type where
    EPlus  : Expr n -> Expr k -> Expr (nMax n k)
    EMinus : Expr n -> Expr k -> Expr (nMax n k)
    EMult  : Expr n -> Expr k -> Expr (nMax n k)
    EDiv   : Expr n -> Expr k -> Expr (nMax n k)
    EConst : Ratio  -> Expr 0
    EVar   : (n : Nat) -> Expr (S n)
    ESubExp: Expr n -> (p : Vect n (k ** Expr k)) ->
                 Expr ((nFold Main.nMax Z . map DPair.fst) p)
    EId    : String -> (n : Nat) -> Expr n

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

data ContextFree : Expr n -> Type where
    CFConst : ContextFree (EConst r)
    CFVar   : ContextFree (EVar v)
    CFPlus  : ContextFree a -> ContextFree b -> ContextFree (EPlus  a b)
    CFMinus : ContextFree a -> ContextFree b -> ContextFree (EMinus a b)
    CFMult  : ContextFree a -> ContextFree b -> ContextFree (EMult  a b)
    CFDiv   : ContextFree a -> ContextFree b -> ContextFree (EDiv   a b)
    CFSExp  : ContextFree b -> (p : Vect n (k ** z : Expr k ** ContextFree z))
                            -> ContextFree (ESubExp b (map fst p))

nMaxIsAddition : (n : Nat) -> (k : Nat) -> (m ** n + m = nMax n k)
nMaxIsAddition Z _ = (_ ** Refl)
nMaxIsAddition (S n) Z = (0 ** rewrite plusZeroRightNeutral n in Refl)
nMaxIsAddition (S n) (S m) = let (m ** prf) = nMaxIsAddition n m in
    (_ ** rewrite sym prf in Refl)

nMaxLemma1 : Vect (nMax n k) a -> Vect n a
nMaxLemma1 {n} {k} prf = let (x ** p) = nMaxIsAddition n k
                          in take n {m = x} (rewrite p in prf)

nMaxLemma2 : Vect (nMax n k) a -> Vect k a
nMaxLemma2 {n} {k} prf = nMaxLemma1 {n=k} {k=n}
    (rewrite nMaxCommutative k n in prf)

natToFin' : (k : Nat) -> (n : Nat) -> {auto ok : k `LT` n} -> Fin n
natToFin' Z (S n) = FZ
natToFin' (S k) (S n) {ok} = FS (natToFin' k n {ok = fromLteSucc ok})

eval : Expr m -> Vect m Ratio -> Ratio
eval (EConst c)   _ = c
eval (EVar n)     v = natToFin' n (S n) {ok = lteRefl} `index` v
eval (EPlus  a b {n} {k}) v = eval a (nMaxLemma1 v) + eval b (nMaxLemma2 v)
eval (EMult  a b {n} {k}) v = eval a (nMaxLemma1 v) * eval b (nMaxLemma2 v)
eval (EDiv   a b {n} {k}) v = eval a (nMaxLemma1 v) / eval b (nMaxLemma2 v)
eval (EMinus a b {n} {k}) v = eval a (nMaxLemma1 v) - eval b (nMaxLemma2 v)
eval g@(ESubExp b p {n}) v = eval b (map (f n p v) range)
  where f : (n : Nat) -> (p : Vect n (k ** Expr k)) ->
            Vect ((nFold Main.nMax Z . map DPair.fst) p) Ratio -> Fin n -> Ratio
        f Z _ _ _ impossible
        f (S n) ((k ** z) :: ps) xs FZ = eval z (nMaxLemma1 xs)
        f (S n) (p :: ps) xs (FS b) = f n ps (nMaxLemma2 xs) b
eval (EId _ _) _ = 0

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

data Lexeme = OpBrac
            | ClBrac
            | Comma
            | Plus
            | Minus
            | Slash
            | Asterisk
            | Equals
            | Apostrophe
            | Newline
            | Number Integer
            | Identifier String

Eq Lexeme where
  OpBrac          == OpBrac          = True
  ClBrac          == ClBrac          = True
  Comma           == Comma           = True
  Plus            == Plus            = True
  Minus           == Minus           = True
  Slash           == Slash           = True
  Asterisk        == Asterisk        = True
  Equals          == Equals          = True
  Apostrophe      == Apostrophe      = True
  Newline         == Newline         = True
  (Number n1)     == (Number n2)     = n1 == n2
  (Identifier s1) == (Identifier s2) = s1 == s2
  _               == _               = False

lexer : List Char -> List Lexeme
lexer [] = []
lexer xss@(x::xs) = case special x of
        Just a => a :: lexer xs
        Nothing => if isSpace x then lexer xs
        else if isDigit x then let (cr, rs) = break (not . isDigit) xss
              in Number (cast (pack cr)) :: lexer (assert_smaller xss rs)
        else let (cr, rs) = break (\x => isSpace x || isJust (special x)) xss
              in Identifier (pack cr) :: lexer (assert_smaller xss rs)
    where special : Char -> Maybe Lexeme
          special = flip List.lookup [
                        ('(', OpBrac),
                        (')', ClBrac),
                        (',', Comma),
                        ('+', Plus),
                        ('-', Minus),
                        ('/', Slash),
                        ('*', Asterisk),
                        ('=', Equals),
                        ('\'', Apostrophe),
                        ('\n', Newline)]

data Parser a = MkParser (List Lexeme -> (List (a, List Lexeme)))

Functor Parser where
    map f (MkParser g) = MkParser (map (\(a, ns) => (f a, ns)) . g)

Applicative Parser where
    pure a = MkParser (\s => [(a, s)])
    (MkParser ab) <*> (MkParser a) = MkParser (
        concatMap (\(f, ns) => map (\(b, nns) => (f b, nns)) (a ns)) . ab)

Monad Parser where
    (MkParser a) >>= f = MkParser (
        concatMap (\(as, ns) => let MkParser b = f as in b ns) . a)

Alternative Parser where
    empty = MkParser (const [])
    (MkParser a) <|> (MkParser b) = MkParser (\s =>
        let as = a s in if isNil as then b s else a s)

parse : Parser a -> List Lexeme -> List a
parse (MkParser f) = map fst . filter (isNil . snd) . f

expectImpl : (Lexeme -> Maybe a) -> Parser a
expectImpl f = MkParser (\s => case s of
    [] => []
    (x :: xs) => map (\a => (a, xs)) (toList (f x)))

expect : Lexeme -> Parser Lexeme
expect a = expectImpl (\x => if x == a then Just x else Nothing)

some : Parser a -> Parser (List a)
some (MkParser f) = MkParser g
    where g : List Lexeme -> List (List a, List Lexeme)
          g xs = ([], xs) :: concatMap (\(c, ns) =>
                  map (\(cn, nns) => (c :: cn, nns)) (g (assert_smaller xs ns)))
                  (f xs)

many : Parser a -> Parser (l : List a ** NonEmpty l)
many p = let MkParser f = some p in MkParser (g . f)
    where g : List (List a, List Lexeme)
              -> List ((l : List a ** NonEmpty l), List Lexeme)
          g [] = []
          g (([], lex)::as) = g as
          g (((x :: xs), lex)::as) = (((x :: xs) ** IsNonEmpty), lex) :: g as

maybe : Parser a -> Parser (Maybe a)
maybe (MkParser f) = MkParser (\s =>
    (Nothing, s) :: map (\(a, ns) => (Just a, ns)) (f s))

p_number : Parser Integer
p_number = expectImpl (\x => case x of
    Number n => Just n
    _ => Nothing)

p_identifier : Parser String
p_identifier = expectImpl (\x => case x of
    Identifier i => Just i
    _ => Nothing)

p_commasep : Parser a -> Parser (l : List a ** NonEmpty l)
p_commasep p = f <$> some (p <* expect Comma) <*> p
  where f : List a -> a -> (l: List a ** NonEmpty l)
        f as a = (a :: as ** IsNonEmpty)

-- Idris fails if it's not a separate function
wtf : List (n ** Expr n) -> (m ** Vect m (n ** Expr n))
wtf l = toVect l

p_expr : Parser (n ** Expr n)
p_expr = (econstp <$> (maybe (expect Plus) *> p_number))
     <|> (econstm <$> (expect Minus *> p_number))
     <|> (eid <$> p_identifier <*> maybe (expect OpBrac *>
         p_commasep p_expr <* expect ClBrac))
     <|> (expect OpBrac *> p_expr <* expect ClBrac)
     <|> (eop <$> p_expr <*>
         (expect Plus <|> expect Minus <|> expect Slash <|> expect Asterisk) <*>
         p_expr)
    where econstp s = (_ ** EConst (fromInteger s))
          econstm s = (_ ** EConst (fromInteger (-s)))
          eid s ps = case ps of
              Nothing => (_ ** EId s 0)
              Just (l ** _) => let (n ** v) = wtf l
                               in (_ ** ESubExp (EId s n) v)
          eop e1 op e2 = let (e1n ** e1') = e1
                             (e2n ** e2') = e2
                          in case op of
                              Plus => (_ ** EPlus e1' e2')
                              Minus => (_ ** EMinus e1' e2')
                              Asterisk => (_ ** EMult e1' e2')
                              Slash => (_ ** EDiv e1' e2')
                              _ => (_ ** EId "" 0)
