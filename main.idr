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
    ESubExp: Expr (S n) -> (p : Vect (S n) (k ** Expr k)) ->
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
    CFSExp  : ContextFree b ->
              (p : Vect (S n) (k ** z : Expr k ** ContextFree z)) ->
              ContextFree (ESubExp b (map fst p))

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
eval (EPlus  a b) v = eval a (nMaxLemma1 v) + eval b (nMaxLemma2 v)
eval (EMult  a b) v = eval a (nMaxLemma1 v) * eval b (nMaxLemma2 v)
eval (EDiv   a b) v = eval a (nMaxLemma1 v) / eval b (nMaxLemma2 v)
eval (EMinus a b) v = eval a (nMaxLemma1 v) - eval b (nMaxLemma2 v)
eval g@(ESubExp b p {n}) v = eval (assert_smaller g b)
    (map ((\(_ ** (z, xs)) => eval (assert_smaller g z) xs) . f n p v) range)
  where f : (n : Nat) -> (p : Vect (S n) (k ** Expr k)) ->
            Vect ((nFold Main.nMax Z . map DPair.fst) p) Ratio -> Fin (S n) ->
            (k ** (Expr k, Vect k Ratio))
        f _ ((_ ** z) :: ps) xs FZ = (_ ** (z, nMaxLemma1 xs))
        f (S _) (_ :: ps) xs (FS b) = f _ ps (nMaxLemma2 xs) b
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
            | Semicolon
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
  Semicolon       == Semicolon       = True
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
                        (';', Semicolon),
                        ('\'', Apostrophe),
                        ('\n', Newline)]

data Parser a = MkParser (List Lexeme -> (List (a, List Lexeme)))

parse' : Parser a -> List Lexeme -> List (a, List Lexeme)
parse' (MkParser p) s = p s

Functor Parser where
    map f (MkParser g) = MkParser (map (\(a, ns) => (f a, ns)) . g)

Applicative Parser where
    pure a = MkParser (\s => [(a, s)])
    ab <*> a = MkParser (
        concatMap (\(f, ns) => map (\(b, nns) => (f b, nns)) (parse' a ns)) .
        parse' ab)

Monad Parser where
    (MkParser a) >>= f = MkParser (
        concatMap (\(as, ns) => let MkParser b = f as in b ns) . a)

Alternative Parser where
    empty = MkParser (const [])
    a <|> b = MkParser (\s => parse' a s ++ parse' b s)

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

p_commasep_impl : Lexeme -> Parser a -> Parser (l : List a ** NonEmpty l)
p_commasep_impl x p = f <$> some (p <* expect x) <*> p
    where f : List a -> a -> (l: List a ** NonEmpty l)
          f [] a = ([a] ** IsNonEmpty)
          f (a::as) a' = (a :: (as ++ [a']) ** IsNonEmpty)

p_commasep : Parser a -> Parser (l : List a ** NonEmpty l)
p_commasep = p_commasep_impl Comma

p_parlist : Parser a -> Parser (List a)
p_parlist p = f <$> Main.maybe (expect OpBrac *> p_commasep p <* expect ClBrac)
    where f : Maybe (l : List a ** NonEmpty l) -> List a
          f Nothing = []
          f (Just (xs ** _)) = xs

p_fin : Parser ()
p_fin = MkParser (\s => case s of
    [] => [((), [])]
    _  => [])

econstp : Integer -> Expr 0
econstp s = EConst (fromInteger s)

econstm : Integer -> Expr 0
econstm s = EConst (fromInteger (-s))

eid : String -> List (Expr 0) -> Expr 0
eid s ps = case toVect ps of
        (Z ** []) => EId s Z
        (S n ** (x :: xs)) => let k = map f (x :: xs)
            in rewrite g (x :: xs) in (ESubExp (EId s (S n)) k)
    where f : Expr 0 -> (n ** Expr n)
          f e = (0 ** e)
          g : (xss : Vect n (Expr 0)) ->
              Z = nFold Main.nMax Z (map DPair.fst (map f xss))
          g [] = Refl
          g (x :: xs) = rewrite g xs in Refl

eop : Expr 0 -> Lexeme -> Expr 0 -> Expr 0
eop e1 op e2 = case op of
    Plus => EPlus e1 e2
    Minus => EMinus e1 e2
    Asterisk => EMult e1 e2
    Slash => EDiv e1 e2
    _ => EId "" 0

p_expr : Parser (Expr 0)
p_expr = (eop <$> p_expr2 <*> (expect Plus <|> expect Minus) <*> p_expr)
     <|> (expect OpBrac *> p_expr <* expect ClBrac)
     <|> p_expr2
    where aexpr : Parser (Expr 0)
          aexpr = (econstp <$> (maybe (expect Plus) *> p_number))
              <|> (econstm <$> (expect Minus *> p_number))
              <|> (eid <$> p_identifier <*> p_parlist p_expr)
              <|> (expect OpBrac *> p_expr <* expect ClBrac)
          p_expr2 = (eop <$> aexpr <*> expect Asterisk <*> p_expr2)
                <|> (eop <$> aexpr <*> expect Slash <*> aexpr)
                <|> (expect OpBrac *> p_expr2 <* expect ClBrac)
                <|> aexpr

data Statement : Type where
    SAssign : String -> Vect n String -> Expr 0 -> Statement
    SEval : Expr 0 -> Statement

p_stat : Parser Statement
p_stat = (sassign <$> p_identifier <*> p_parlist p_identifier <*>
          (expect Equals *> p_expr))
     <|> (SEval <$> p_expr)
    where sassign : String -> List String -> Expr 0 -> Statement
          sassign s p e = SAssign s (DPair.snd (toVect p)) e

var_subst : Expr n -> String -> Expr m -> (k ** Expr k)
var_subst e s (EConst c) = (_ ** EConst c)
var_subst e s (EVar v)   = (_ ** EVar v)
var_subst e s (ESubExp b p {n}) =
      let (n' ** nb) = var_subst e s b
          np = map (f e s) p
       in case decEq (S n) n' of
           Yes Refl => (_ ** ESubExp nb np)
           No _ => (_ ** ESubExp b np)
    where f : Expr m -> String -> (z ** Expr z) -> (k ** Expr k)
          f e s (_ ** p) = var_subst e s p
var_subst e {n} s (EId s2 n2) = if s == s2
            then (n ** e)
            else (_ ** EId s2 n2)
var_subst e s (EPlus a1 a2) = let (k1 ** p1) = var_subst e s a1
                                  (k2 ** p2) = var_subst e s a2
                               in (_ ** EPlus p1 p2)
var_subst e s (EMinus a1 a2) = let (k1 ** p1) = var_subst e s a1
                                   (k2 ** p2) = var_subst e s a2
                                in (_ ** EMinus p1 p2)
var_subst e s (EMult a1 a2) = let (k1 ** p1) = var_subst e s a1
                                  (k2 ** p2) = var_subst e s a2
                               in (_ ** EMult p1 p2)
var_subst e s (EDiv  a1 a2) = let (k1 ** p1) = var_subst e s a1
                                  (k2 ** p2) = var_subst e s a2
                               in (_ ** EDiv p1 p2)

Context : Type
Context = List (String, (n ** Expr n))

mass_subst : Expr m -> Context -> (k ** Expr k)
mass_subst e [] = (_ ** e)
mass_subst e ((s, (_ ** e')) :: xs) = let (_ ** p) = var_subst e' s e
                                       in mass_subst p xs

step : Context -> Statement -> (Maybe Ratio, Context)
step ctx (SAssign s v {n} e) =
        let ctx' = toList (map (\(r, s) => (s, (_ ** EVar (finToNat r))))
                                           (Vect.zip range v))
         in (Nothing, (s, mass_subst e (ctx' ++ ctx)) :: ctx)
step ctx (SEval e) = let (n ** e') = mass_subst e ctx
                      in case n of
                          Z => (Just (eval e' []), ctx)
                          S n => (Nothing, ctx)

p_prog : Parser (l : List Statement ** NonEmpty l)
p_prog = p_commasep_impl Semicolon p_stat

exec : List Statement -> List Ratio
exec ls = catMaybes (exec' List.Nil ls)
    where exec' : Context -> List Statement -> List (Maybe Ratio)
          exec' _ [] = []
          exec' ctx (x :: xs) = let (res, nctx) = step ctx x
              in res :: exec' nctx xs

run : String -> List Ratio
run s = case (head' . parse p_prog . lexer . unpack) s of
    Nothing => []
    Just (a ** _) => exec a
