{-# LANGUAGE TemplateHaskell, QuasiQuotes, LambdaCase, GeneralizedNewtypeDeriving #-}

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
- We call applicative brackets @⟦..⟧@ which replace @$(applicative [|..|])@.
- We call effectful brackets @⟨..⟩@ which replace @(_(..))@

The previous example now reads:

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
applicative brackets ⟦..⟧. The only restriction is that
inside a effectful bracket ⟨..⟩ only free variables are allowed, that is variables
that are defined outside the applicative brackets ⟦..⟧.
As a corollary, if the result of a effectful expression (enclosed in ⟨..⟩)
is bound to a variable (by a let, case, lambda, lambdaCase,
or where) then that variable cannot be used inside another
effectful expression (enclosed in ⟨..⟩).
Another corollary is that if a local function is defined inside applicative brackets ⟦..⟧,
then its parameters may not be used inside effectful brackets ⟨..⟩.

NOTE: the infix brackets cannot be used around effectful expressions:

>>>  ⟦ x `⟨expr⟩` y ⟧ -- ILLEGAL

TODO: use the original expression to display a nice error message.

-}

module Grammar.SafeAG.TH.Applicative (applicative) where
import Prelude hiding (exp)
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Set (Set)
import Data.Map (Map)
import Data.List (intersperse)
import Control.Monad
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.Except
import Language.Haskell.TH hiding (match, clause)

err s = error $ "applicative: " ++ s

-- now `restrictKeys` is exported by Map.
restrictKeys :: Ord k => Map k a -> Set k -> Map k a
restrictKeys m s =
  Map.filterWithKey (\k _ -> k `Set.member` s) m


--------------------------------------------------
newtype ListF a = ListF ([a] -> [a])
list :: [a] -> ListF a
(++.) :: ListF a -> ListF a -> ListF a
toList :: ListF a -> [a]
nil :: ListF a
cons, (.:) :: a -> ListF a -> ListF a

list xs = ListF (xs++)
ListF x ++.ListF y = ListF (x . y)
toList (ListF f) = f []
nil = list []
x .: xs = list [x] ++. xs
cons = (.:)

instance Monoid (ListF a) where
  mempty = nil
  mappend = (++.)

--------------------------------------------------
applicative qe = do
  (e, xs, as) <- runPullQ . exp =<< qe
  let f = if null xs then e else LamE (VarP <$> xs) e
  return $ liftE f as

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

{- Later the error type might include line and column number. -}
newtype Error = Error String
instance Show Error where
    show (Error s) = s

type Env = Map Name Binder -- bound variables together with the construct that binds them.
type BVars = Set Name -- bound variables
type FVars = Set Name -- free variables

newtype PullQ a = PullQ {fromPullQ :: ReaderT Env (ExceptT Error (WriterT (ListF (Name, Exp)) Q)) a}
  deriving (Functor, Applicative, Monad, MonadReader Env, MonadError Error, MonadWriter (ListF (Name, Exp)))

runPullQ :: PullQ a -> Q (a, [Name], [Exp])
runPullQ (PullQ f) = do
  (e', es) <- runWriterT (runExceptT (runReaderT f Map.empty))
  case e' of
    Left msg -> fail $ "Applicative notation: " ++ show msg
    Right e -> do
      let (xs, as) = unzip (toList es)
      return (e, xs, as)

liftQ :: Q a -> PullQ a
liftQ q = PullQ . lift .lift . lift $ q

check :: Exp -> PullQ ()
check e = do
  m <- ask
  let vs = Map.keysSet m
  let bad = Set.intersection vs (free e)
  unless (Set.null bad)
    $ throwError $ Error $
      "illegal use of: " ++ ppr_set bad
      ++ "\nin effectful expression: ⟨" ++ pprint e ++ "⟩\n"
      ++ bound_msg (inverseMap (restrictKeys m bad))
      ++ "\nThe variables bound inside the applicative brackets must not occur inside an effectful expression.\n"

bound_msg = Map.foldWithKey msg ""
  where
    msg b vs s = ppr_set vs ++ " bound in the " ++ show b ++ "\n" ++ s

inverseMap :: (Ord k, Ord a) => Map k a -> Map a (Set k)
inverseMap = Map.foldWithKey ins Map.empty
  where ins k x = Map.insertWith (\/) x (single k)

ppr_set s = concat $ intersperse ", " $ pprint <$> Set.toList s

-- Bind an effectful expression to a new name and return that name

bind :: Exp -> PullQ Name
bind e = do
  check e
  x <- liftQ $ newName "x"
  tell (list [(x,e)])
  return x

-- the surrounding structure that binds a variable
data Binder =
  ExpBd Exp | DecBd Dec | MatchBd Match | ClauseBd Name Clause
  deriving (Eq, Ord)

instance Show Binder where
  show = \case
     ExpBd e      -> "expression "  ++ pprint e
     DecBd d      -> "declaration " ++ pprint d
     MatchBd m    -> "match "       ++ pprint m
     ClauseBd f c -> "clause "      ++ pprint f ++ " " ++ pprint c

upd_env :: BVars -> Binder -> PullQ a -> PullQ a
upd_env ns b p = local (Map.union new_env) p
  where new_env = Set.foldr (\k -> Map.insert k b) Map.empty ns

upd_env_p p = upd_env_pd p []
upd_env_d d = upd_env_pd [] d
upd_env_pd p d = upd_env (pat_bounds p \/ dec_bounds d)

exp :: Exp -> PullQ Exp
exp e0 = case e0 of
  AppE (UnboundVarE n) e | nameBase n == "_" -> VarE <$> bind e
  AppE f e -> AppE <$> exp f <*> exp e
  InfixE (Just l) o (Just r) -> inf <$> exp o <*> exp l <*> exp r
    where inf o l r = InfixE (Just l) o (Just r)
  InfixE Nothing o (Just r) -> inf <$> exp o <*> exp r
    where inf o r = InfixE Nothing o (Just r)
  InfixE (Just l) o Nothing -> inf <$> exp o <*> exp l
    where inf o l = InfixE (Just l) o Nothing
  InfixE Nothing o Nothing -> inf <$> exp o
    where inf o = InfixE Nothing o Nothing
  UInfixE l o r ->
    uinf <$> exp o <*> exp l <*> exp r
    where uinf o l r = UInfixE l o r
  LamE ps e -> upd_env_p ps b0 $ LamE ps <$> exp e
  LetE ds e -> upd_env_d ds b0 $ LetE <$> decs ds <*> exp e
  CaseE e ms      ->  CaseE <$> exp e <*> matches ms
  LamCaseE ms     ->  LamCaseE <$> matches ms
  CondE c e t     ->  CondE <$> exp c <*> exp e <*> exp t
  TupE es         ->  TupE <$> exps es
  UnboxedTupE es  ->  UnboxedTupE <$> exps es
  ListE es        ->  ListE <$> exps es
  ParensE e       ->  ParensE <$> exp e
  MultiIfE cs     ->  MultiIfE <$> guardedexps cs
  DoE ss          ->  DoE <$> stmts ss
  CompE ss        ->  CompE <$> stmts ss
  ArithSeqE r     ->  ArithSeqE <$> range r
  SigE e t        ->  (\e -> SigE e t) <$> exp e
  RecConE n fs    ->  RecConE n <$> fields fs
  RecUpdE e fs    ->  RecUpdE <$> exp e <*> fields fs
  StaticE e       ->  StaticE <$> exp e
  -- Any other expression is left unchanged (VarE, ConE, LitE, UboundVarE)
  e  ->  return e
 where b0 = ExpBd e0

exps = traverse exp

dec :: Dec -> PullQ Dec
dec d = case d of
  FunD n cs   -> FunD n <$> clauses n cs
  ValD p b ds -> ValD p <$> upd_env_pd [p] ds (DecBd d) (body b) <*> decs ds
  d           -> return d
decs = traverse dec

match :: Match -> PullQ Match
match m@(Match p b ds) =
  Match p
  <$> upd_env_pd [p] ds (MatchBd m) (body b)
  <*> decs ds

matches = traverse match

stmt :: Stmt -> PullQ Stmt
stmt = \case
  BindS p e -> BindS p <$> exp e
  LetS ds -> LetS <$> decs ds
  NoBindS e -> NoBindS <$> exp e
  ParS sss -> ParS <$> traverse stmts sss
stmts = traverse stmt

range :: Range -> PullQ Range
range = \case
  FromR e           -> FromR <$> exp e
  FromThenR x y     -> FromThenR <$> exp x <*> exp y
  FromToR x y       -> FromToR <$> exp x <*> exp y
  FromThenToR x y z -> FromThenToR <$> exp x <*> exp y <*> exp z

body = \case
  NormalB e -> NormalB <$> exp e
  GuardedB gs -> GuardedB <$> guardedexps gs

pair :: (a,Exp) -> PullQ (a,Exp)
pair (x, e) = (\e -> (x,e)) <$> exp e
pairs = traverse pair
guardedexps = pairs
fields = pairs

clause n c@(Clause ps b ds) =
  Clause ps
  <$> upd_env_pd ps ds (ClauseBd n c) (body b)
  <*> decs ds

clauses = traverse . clause

--------------------------------------------------
-- free and bound variables

infixr 5 \/
(\/),(\\) :: Ord a => Set a -> Set a -> Set a
(\/) = Set.union
(\\) = Set.difference
single = Set.singleton

free :: Exp -> FVars
free = \case
  InfixE (Just l) o (Just r) -> frees [l,o,r]
  InfixE Nothing o (Just r)  -> frees [o,r]
  InfixE (Just l) o Nothing  -> frees [l,o]
  InfixE Nothing o Nothing   -> free o
  UInfixE l o r              -> frees [l,o,r]
  AppE f e       -> frees [f,e]
  LamE ps e      -> free e \\ pat_bounds ps
  LetE ds e      -> free e \\ dec_bounds ds
  CaseE e ms     -> free e \/ match_frees ms
  LamCaseE ms    -> match_frees ms
  CondE c e t    -> frees [c,e,t]
  TupE es        -> frees es
  UnboxedTupE es -> frees es
  ListE es       -> frees es
  ParensE e      -> free e
  MultiIfE ges   -> frees (snd <$> ges)
  DoE ss         -> stmt_frees ss
  CompE ss       -> stmt_frees ss
  ArithSeqE r    -> range_free r
  SigE e t       -> free e
  RecConE n fs   -> frees (snd `map` fs)
  RecUpdE e fs   -> frees (e : snd `map` fs)
  StaticE e      -> free e
  UnboundVarE n  -> single n
  ConE _         -> Set.empty
  LitE _         -> Set.empty
  VarE n         -> single n

unionMap f = Set.unions . map f
frees = unionMap free
match_frees = unionMap match_free

match_free (Match p b ds) =
  body_free b \\ (pat_bound p \/ dec_bounds ds)

body_free = \case
  GuardedB ges -> frees (snd <$> ges)
  NormalB e -> free e

stmt_frees = foldr cons Set.empty
 where
  cons s fs = case s of
    BindS p e -> free e \/ (fs \\ pat_bound p)
    LetS ds   -> fs \\ dec_bounds ds
    NoBindS e -> fs \/ free e
    ParS sss  -> fs \/ unionMap stmt_frees sss

range_free = \case
  FromR e              -> free e
  FromThenR e e'       -> frees [e,e']
  FromToR e e'         -> frees [e,e']
  FromThenToR e e' e'' -> frees [e,e',e'']

dec_bounds = unionMap dec_bound
pat_bounds = unionMap pat_bound

dec_bound = \case
  FunD n cs   -> single n
  ValD p b dc -> pat_bound p
  _           -> Set.empty

pat_bound = Set.fromList . pat_vars

pat_vars :: Pat -> [Name]
pat_vars = \case
  VarP n -> [n]
  p -> pat_vars `concatMap` sub_patterns p

sub_patterns = \case
  TupP ps        -> ps
  UnboxedTupP ps -> ps
  ConP _ ps      -> ps
  InfixP x _ y   -> [x,y]
  UInfixP x _ y  -> [x,y]
  ParensP p      -> [p]
  TildeP p       -> [p]
  BangP p        -> [p]
  AsP _ p        -> [p]
  RecP _ fps     -> snd <$> fps
  ListP ps       -> ps
  SigP p _       -> [p]
  ViewP _ p      -> [p]
  _              -> []

{-
Local Variables:
compile-command: "ghc Applicative"
End:
-}
