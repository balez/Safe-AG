{-# LANGUAGE TemplateHaskell, QuasiQuotes, LambdaCase #-}

{-| @$(applicative [|...|])@ is an alternative to idiom
brackets, for writing expressions over an @Applicative@
functor.  The impure values inside the expression must be put
inside special brackets. Currently the syntax is to use apply
an underscore to tag the impure values:

@
$(applicative [| _(Just 3) + _(Just 2) |] ----> Just 5
$(applicative [| map sum (_(Just [3,2])) |] ---> Just 5
@

For more readability, we suggest using unicode brackets and
replacing them with a preprocessor.

@
⟦ ⟨Just 3⟩ + ⟨Just 2⟩ ⟧----> Just 5
⟦ map sum ⟨Just [3,2]⟩ ⟧ ---> Just 5
@

The syntax supports let expressions that can bind either pure
or impure values:

@
⟦ let x = ⟨foo⟩ in ⟨bar⟩ + x ⟧ == ⟦ ⟨bar⟩ + ⟨foo⟩ ⟧
⟦ let x = baz in ⟨bar⟩ + x ⟧ == ⟦ ⟨bar⟩ + baz ⟧
@

This notation pulls out all the ⟨e⟩ from an expression and
rewrite it as an application, so that:

@
⟦ e[⟨e1⟩ .., ⟨en⟩] ⟧
== pure (\ x1 .. xn . e[x1..xn]) <*> e1 ... <*> en
@
where @⟨e1⟩..⟨en⟩@ occur in the order pre-order traversal of
the expression @e@.

All valid Haskell expressions can be used inside the
applicative brackets, except for the following restriction:
if the result of an effectful expression (enclosed in ⟨..⟩)
is bound to a variable (by a let, case, lambda, lambdaCase,
or where) then that variable cannot be used inside another
effectful expression (enclosed in ⟨..⟩).

TODO: check the previous condition to display a nice error message.
-}

module Grammar.SafeAG.TH.Applicative (applicative) where
import Language.Haskell.TH.Lib hiding (match)
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Syntax

err s = error $ "applicative: " ++ s

--------------------------------------------------
type ListF a = [a] -> [a]
list :: [a] -> ListF a
(++.) :: ListF a -> ListF a -> ListF a
toList :: ListF a -> [a]
nil :: ListF a
cons, (.:) :: a -> ListF a -> ListF a

list xs = (xs++)
(++.) = (.)
toList xs = xs []
nil = list []
x .: xs = list [x] ++. xs
cons = (.:)

--------------------------------------------------
applicative qe = do
  (e', es) <- pull =<< qe
  let (xs, as) = unzip (toList es)
      lam = LamE (VarP <$> xs) e'
  return $ liftE lam as

-- | liftE f [e1..en] == pure f <*> e1 <*> ... <*> en
liftE f es = applies (AppE (VarE 'pure) f : es)
  where applies = foldl1 (infixVar '(<*>))

infixVar op l r = InfixE (Just l) (VarE op) (Just r)
infixCon op l r = InfixE (Just l) (ConE op) (Just r)

--------------------------------------------------
{- @pull x = (y, [(n1,e1)..(nk,ek)]@

where @y@ is obtained from @x@ by replacing the @e1@..@ek@
with variables of names @n1@..@nk@. The @e1..en@ where
all the ⟨⟩-subexpresions in @x@, and @y@
doesn't contain any more of those expression.
-}
type Pull a = (a, ListF (Name, Exp))
type PullQ a = Q (Pull a)

pull :: Exp -> PullQ Exp
pull (AppE (UnboundVarE _) e) = do
  x <- newName "x"
  return (VarE x, list [(x, e)])

pull (AppE f e) = pull2 AppE f e

pull (InfixE (Just l) o (Just r)) = pull3 inf o l r
  where inf o l r = InfixE (Just l) o (Just r)

pull (UInfixE l o r) = pull3 uinf o l r
  where uinf o l r = UInfixE l o r

pull (LamE ps e) = pull1 (LamE ps) e

{- Let expression. It is an error if some of the
   effectful values in the body depend on some other
   effectful values.
-}

pull (LetE d e)       =  with2 (trav dec) pull LetE d e
pull (CaseE e m)      =  with2 pull (trav match) CaseE e m
pull (LamCaseE ms)    =  wtrav match LamCaseE ms
pull (CondE c e t)    =  pull3 CondE c e t
pull (TupE es)        =  pulls TupE es
pull (UnboxedTupE es) =  pulls UnboxedTupE es
pull (ListE es)       =  pulls ListE es
pull (ParensE e)      =  pull1 ParensE e
pull (MultiIfE cs)    =  wtrav guardexp MultiIfE cs
pull (DoE ss)         =  wtrav stmt DoE ss
pull (CompE ss)       =  wtrav stmt CompE ss
pull (ArithSeqE r)    =  with range ArithSeqE r
pull (SigE e t)       =  pull1 (\e -> SigE e t) e
pull (RecConE n fs)   =  wtrav field (RecConE n) fs
pull (RecUpdE e fs)   =  with2 pull (trav field) RecUpdE e fs
pull (StaticE e)      =  pull1 StaticE e

-- Any other expression is left unchanged
-- VarE, ConE, LitE, UboundVarE

pull e = return (e, nil)

--------------------------------------------------
with p c x = do
  (x', xs) <- p x
  return (c x', xs)

with2 p1 p2 c x y = do
  (x', xs) <- p1 x
  (y', ys) <- p2 y
  return (c x' y', xs ++. ys)

with3 p1 p2 p3 c x y z = do
  (x', xs) <- p1 x
  (y', ys) <- p2 y
  (z', zs) <- p3 z
  return (c x' y' z', xs ++. ys ++. zs)

wtrav = with . trav

pull1 = with pull
pull2 = with2 pull pull
pull3 = with3 pull pull pull
pulls = wtrav pull

trav :: (a -> Q (Pull b)) -> [a] -> Q (Pull [b])
trav p x = pull_seq <$> traverse p x

pull_seq :: [Pull a] -> Pull [a]
pull_seq = foldr cons ([], nil)
  where cons (x, xs) (s, ss) = (x:s, xs ++. ss)

--------------------------------------------------

dec :: Dec -> PullQ Dec
dec (ValD p (NormalB e) []) = pull1 (dec p) e
  where dec p e = ValD p (NormalB e) []
dec _ = err "only simple let bindings are accepted."

match :: Match -> PullQ Match
match (Match p (NormalB e) []) = pull1 (match p) e
  where match p e = Match p (NormalB e) []
match _ = err "only simple case expressions are accepted."

stmt :: Stmt -> PullQ Stmt
stmt = \case
  BindS p e -> pull1 (BindS p) e
  LetS ds -> wtrav dec LetS ds
  NoBindS e -> pull1 NoBindS e
  ParS sss -> wtrav (wtrav stmt id) ParS sss

range :: Range -> PullQ Range
range = \case
  FromR e           -> pull1 FromR e
  FromThenR x y     -> pull2 FromThenR x y
  FromToR x y       -> pull2 FromToR x y
  FromThenToR x y z -> pull3 FromThenToR x y z

pair :: (a,Exp) -> PullQ (a,Exp)
pair (x, e) = pull1 (\e -> (x,e)) e

guardexp = pair
field = pair

{-
Local Variables:
compile-command: "ghc Applicative"
End:
-}
