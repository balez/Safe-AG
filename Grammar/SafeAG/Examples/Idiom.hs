{-# LANGUAGE TemplateHaskell, QuasiQuotes, LambdaCase #-}

{-|

Original file by Matt Morrow. Reworked by Florent Balestrieri

Note (FB): I removed the quasiquoter because it doesn't allow
nesting, I find the splice much more useful. Since it is a
bit heavy on syntax, I use a preprocessor (lhs2tex is good
for that) to replace unicode brackets ⟪...⟫ with the splice.

In this file we define the splice 'idiom' ('i' is a synonym).

'idiom' implements the usual idiom brackets, extended with
syntatic sugars for other constructions: tuples, lists, let,
if-then-else.

-}

--module Control.Applicative.QQ.Idiom (idiom, i) where
module Grammar.SafeAG.Examples.Idiom (idiom, i) where
import Data.Word (Word8)
import Control.Applicative ((<*>), pure)
import Data.Traversable (sequenceA)
import Control.Monad ((<=<), liftM2)
import Language.Haskell.Meta (parseExp)
import Language.Haskell.TH.Lib
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Syntax

ifThenElse c t e = if c then t else e
r = return

--------------------------------------------------
bracket :: Exp -> ExpQ

bracket (AppE (UnboundVarE _) e) = liftB e []

bracket (AppE f x) = do
  f' <- bracket f
  return $ infixVar '(<*>) f' x

bracket (InfixE (Just left) op (Just right)) =
  liftB op [left, right]

bracket (UInfixE left op right) = case (left,right) of
  (UInfixE{}, _) -> ambig
  (_, UInfixE{}) -> ambig
  (_, _) -> liftB op [left, right]
 where
  ambig = fail "Ambiguous infix expression in idiom bracket."

bracket (CondE c t e) = do
  f <- [| ifThenElse |]
  liftB f [c, t, e]

bracket (TupE es) =
  let tuple = ConE $ tupleDataName (length es) in
  liftB tuple es

bracket e@(ListE es) =
  [| sequenceA $(r e) |]

bracket (LetE ds e) =
  let (f,es) = lambdafies ds e in
  liftB f es

-- this doesn't make sense
-- bracket (CaseE e ms) = do
--   (f, es) <- casefun ms
--   liftB f (e:es)

bracket e = liftB e []

-- | liftB f [e1..en] == pure f <*> e1 <*> ... <*> en

liftB f es = return $ applies (AppE (VarE 'pure) f : es)
  where applies = foldl1 (infixVar '(<*>))

infixVar op l r = InfixE (Just l) (VarE op) (Just r)
infixCon op l r = InfixE (Just l) (ConE op) (Just r)

{-|
    Transforms a let-expression into an application of a lambda-abstraction
    only let expression of the simple form are accepted:

@
let {p1 = e1, ... pn = en} in e
@

Which will be transformed into:

@
(\p1 ... pn -> e) e1 ... en
@

-}

lambdafies ds e = (lam, es)
  where (ps,es) = unzip (dec_patexp <$> ds)
        lam = LamE ps e

dec_patexp (ValD p (NormalB e) []) = (p,e)
dec_patexp _ = error "idiom: only simple let bindings are accepted."

{-
from a list of matches @(p1 -> e1, .., pn -> en)@ we build a function

@
\x f1 .. fn -> case x of {p1[x1..xn] -> f1 x1..xn; ...}
@

and a list of functions @f1..fn@
-}

casefun ms = do
  let (ps,es) = unzip (match_patexp <$> ms)
  let pvs = pat_vars <$> ps
  let fs = zipWith (\vs e -> LamE (VarP <$> vs) e) pvs es
  let matches = zipWith3 (\p f vs -> Match p (NormalB (foldl AppE (VarE f) (VarE <$> vs))) [])
  x <- newName "x"
  xs <- sequenceA (newName "x" <$ es)
  let lam = LamE (VarP <$> (x:xs))
                 (CaseE (VarE x) (matches ps xs pvs))
  return (lam, fs)

match_patexp (Match p (NormalB e) []) = (p, e)
match_patexp _ = error "idiom: only simple case expressions are accepted."

pat_vars :: Pat -> [Name]
pat_vars = \case
  VarP n -> [n]
  p -> pat_vars `concatMap` sub_patterns p

sub_patterns = \case
  TupP ps -> ps
  UnboxedTupP ps -> ps
  ConP _ ps -> ps
  InfixP x _ y -> [x,y]
  UInfixP x _ y -> [x,y]
  ParensP p -> [p]
  TildeP p -> [p]
  BangP p -> [p]
  AsP _ p -> [p]
  RecP _ fps -> snd <$> fps
  ListP ps -> ps
  SigP p _ -> [p]
  ViewP _ p -> [p]
  _ -> []


{-|

@$('idiom' [|...|])@ is a template haskell splice that
implement idiom brackets plus some syntactic sugar around
common language constructs: tuples, if-then-else, let
expressions.  There is a shortcut @i = idiom@, but the most
confortable way to use the splice is to go through a
preprocessor to replace unicode brackets like @⟪@ and @⟫@
with @$(idiom[|@ and @|]@

>>> ⟪ f e1 e2 ... en ⟫
== pure f <*> e1 <*> e2 ... <*> en

In particular @⟪ f e ⟫ == f <$> e@

>>> ⟪ e1 `binop` e2 ⟫
== ⟪ binop e1 e2 ⟫
== liftA2 binop e1 e2

>>> ⟪ e1 # e2 ⟫
== ⟪ (#) e1 e2 ⟫
== liftA2 (#) e1 e2

Where (#) is any operator symbol

Let expressions: the declarations must be non-recursive,
each @e1@...@en@ must be applicative and @e@ must be pure.

>>> ⟪ let {p1 = e1; ...; pn = en} in e ⟫
== ⟪ (\p1 ... pn -> e) e1 .. en ⟫

>>> ⟪ if e1 then e2 else e3 ⟫
== ⟪ (\x1 x2 x3 -> if x1 then x2 else x3) e1 e2 e3 ⟫

>>> ⟪ (e1, e2, .., en) ⟫
== ⟪ (\x1 .. xn -> (x1,..,xn)) e1 .. en ⟫

>>> ⟪ [e1, .., en] ⟫
== ⟪ (\x1 .. xn -> [x1,..,xn]) e1 .. en ⟫
== sequenceA [e1,..en]

Sometimes, we want to apply a function to pure arguments,
we provide a shortcut:

@
⟪ _(f e1 .. en) ⟫ == pure (f e1 .. en)
== ⟪ f ⟪e1⟫ ... ⟪en⟫ ⟫
@

More generally, @⟪_e⟫ == pure e@

Any other case:

>>> ⟪ x ⟫
pure x

-}

idiom = (>>= bracket)
i = idiom

{-
Local Variables:
compile-command: "ghc Idiom"
End:
-}
