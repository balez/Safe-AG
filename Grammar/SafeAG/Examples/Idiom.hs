{-# LANGUAGE TemplateHaskell, QuasiQuotes, LambdaCase #-}

{-|
In this file we define the splice 'idiom' ('i' is a synonym).

'idiom' implements the usual idiom brackets, extended with
syntatic sugars for other constructions.

Contrary to the applicative_quoter of Matt Morrow, I chose
not to use a quasiquoter because it doesn't allow
nesting. Nesting is very important and therefore I find the
splice much more useful, but since it is a bit heavy on
syntax (especially when nesting), I use a preprocessor
(lhs2tex is good for that) to replace unicode brackets ⟪...⟫
with the splice.

@
%format ⟪ = "$(idiom[|"
%format ⟫ = "|])"
@

Or if you prefer sed:

@
s_⟪_$(idiom[|_g
s_⟫_|])_g
@
-}

--module Control.Applicative.TH.Idiom (idiom, i) where
module Grammar.SafeAG.Examples.Idiom (idiom, i, returnA) where
import Language.Haskell.TH.Lib
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Syntax

-- to be used with applicative do
returnA = id

ifThenElse c t e = if c then t else e
r = return

--------------------------------------------------
bracket :: Exp -> ExpQ

bracket (AppE (UnboundVarE _) e) =
  liftQ e []

bracket (AppE f x) = do
  f' <- bracket f
  return $ infixVar '(<*>) f' x

bracket (InfixE (Just left) op (Just right)) =
  liftQ op [left, right]

bracket (UInfixE left op right) = case (left,right) of
  (UInfixE{}, _) -> ambig
  (_, UInfixE{}) -> ambig
  (_, _) -> liftQ op [left, right]
 where
  ambig = fail "Ambiguous infix expression in idiom bracket."

bracket (CondE c t e) = do
  f <- [| ifThenElse |]
  liftQ f [c, t, e]

bracket (TupE es) = liftQ tuple es
  where tuple = ConE $ tupleDataName (length es)


bracket e@(ListE es) =
  [| sequenceA $(r e) |]

bracket (DoE stmts) =
  bindings "do {p1 <- e1; ...; pn <- en; e}" stmts
bracket (CompE stmts) =
  bindings "[ e | p1 <- e1, .. pn <- en]" stmts

bracket (LetE ds e) =
  return (lets ds e)

bracket (CaseE e ms) =
  liftQ (LamCaseE ms) [e]

bracket e = liftQ e []

-- | liftE f [e1..en] == pure f <*> e1 <*> ... <*> en

liftE f es = applies (AppE (VarE 'pure) f : es)
  where applies = foldl1 (infixVar '(<*>))

infixVar op l r = InfixE (Just l) (VarE op) (Just r)
infixCon op l r = InfixE (Just l) (ConE op) (Just r)

liftQ f es = return $ liftE f es

{- ⟪ do {p1 <- e1; ...; pn <- en; e} ⟫
   --> ⟪ (\p1 ... pn -> e) e1 .. en ⟫
-}

bindings form stmts = liftQ lam exps
  where
    (pats, exps) = unzip $ fromBindS form <$> init stmts
    lam = LamE pats (fromNoBindS form $ last stmts)

error_bindings form =
  error $ "idiom: expected an expression of the form '" ++ form ++ "'"

fromBindS form (BindS p e) = (p,e)
fromBindS form _ = error_bindings form
fromNoBindS form (NoBindS e) = e
fromNoBindS form _ = error_bindings form

lets :: [Dec] -> Exp -> Exp
lets [] e = e
lets [d] e = let1 d e
lets (d:ds) e = let1 d (lets ds e)

let1 d = LetE decls
 where
  (pat, arg) = decl_patexp d
  vars = pat_vars pat
  matches = var_match pat <$> vars
  exps = (\f -> liftE f [arg]) <$> matches
  dec n e = ValD (VarP n) (NormalB e) []
  decls = zipWith dec vars exps

decl_patexp (ValD p (NormalB e) []) = (p,e)
decl_patexp _ = error "idiom: only simple let bindings are accepted."

var_match p n =
  LamCaseE [Match p (NormalB (VarE n)) []]

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
implements idiom brackets generalised with some syntactic
sugar around common language constructs:

- function application
- infix operators
- conditionals
- case expressions
- applicative do: @do {p1 <- e1, .., pn <- en; e}@
- applicative comprehension @[ e | p1 <- e1, .., pn <- en]@
- tuples
- lists
- let expressions

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

Conditional expressions.

>>> ⟪ if e1 then e2 else e3 ⟫
== ⟪ (\x1 x2 x3 -> if x1 then x2 else x3) e1 e2 e3 ⟫

Case expressions: @e@ must be applicative, @e1..en@ must be pure.

>>> ⟪ case e of {p1 -> e1; ... pn -> en} ⟫
== ⟪ (\x -> case x of {p1 -> e1; ... pn -> en}) e ⟫

Applicative comprehension: only the following form is
accepted.  Each @e1@...@en@ must be applicative and may not
refer to previous bindings. @e@ must be pure.

>>> ⟪ [ e | p1 <- e1; ...; pn <- en ] ⟫
== ⟪ (\p1 ... pn -> e) e1 .. en ⟫

Do expressions: only the following form is accepted.  each
@e1@...@en@ must be applicative and may not refer to previous
bindings.  @e@ must be pure.

>>> ⟪ do {p1 <- e1; ...; pn <- en; e} ⟫
== ⟪ [e | p1 <- e1; ...; pn <- en] ⟫

Tuples.

>>> ⟪ (e1, e2, .., en) ⟫
== ⟪ (\x1 .. xn -> (x1,..,xn)) e1 .. en ⟫

Lists.

>>> ⟪ [e1, .., en] ⟫
== ⟪ (\x1 .. xn -> [x1,..,xn]) e1 .. en ⟫
== sequenceA [e1,..en]

Let expressions. @e1@ and @e2 must be applicative. The
variables @x1..xn@ are also applicative in the expression
@e2@. Note that this construct will repeat the effects of
@e1@ for each of the pattern variables @x1..xn@ used @e2@,
since each @m1@ is a pattern match over @e1@.

>>> ⟪ let p1[x1...xn] = e1 in e2 ⟫
== let {x1 = m1; ... xn = mn} in e2

where p1[x1 := m1, ... xn := mn] == e1

A let expression may contains many declarations, but there
must be no mutual recursion, no left to right dependencies.
Such lets are transformed into simpler lets as follows:

>>> ⟪ let {p1 = e1; p2 = e2; .. pn = en} in e3 ⟫
== ⟪ let p1 = e1 in let {p2 = e2; .. pn = en} in e3 ⟫

Examples:
>>> ⟪ let (x,y) = a in x ⟫
== ⟪ (\x y -> x) a ⟫
== ⟪ fst a ⟫

>>> ⟪ let (x,y) = a in ⟪ x + y ⟫ ⟫
== ⟪ ⟪ fst a ⟫ + ⟪ snd a ⟫ ⟫

>>> ⟪ let (x,y) = a in ⟪ (x,y) ⟫ ⟫
== a

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
