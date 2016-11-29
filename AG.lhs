* Overview
EDSL for attribute grammars in Haskell.

This library defines first-class attribute grammars
objects. This allows to write compilers modularly.  Our
approach is distinct to the previous attempts in that it is
both lightweight and type safe.

Other first-class implementation of attribute grammars in
Haskell are:

- [Moor] :: Light-weight approach with no type safety.
- [Viera] :: Type-safe approach with complex types and classes.
- [Balestrieri] :: Type-safe approach with complex types and classes.

Our lightweight approach ensures a clean public interface for
the user with simple types and simple error messages that do
not leak implementation details, unlike [Viera] and
[Balestrieri]. In addition, the grammars are thoroughly
checked unlike with the simple approach of [Moor].

To achieve this, our approach involves two typechecking
phases.  This first is the static typechecking by the
compiler where the type of attributes and their kind
(inherited, synthesized, or terminals) is checked
statically. The second phase checks that the attribtion rules
are complete for a given grammar, that the concrete tree type
is compatible with the grammar, and that the concrete input
and output types are compatible with the attribution rules.
This second phase occurs at runtime, however it should not be
confused with dynamic typing: in contrast, the runtime
typechecking is done once and for all, whereas dynamic typing
involves doing testing the types every time a function is
used and may fail if the type mismatch. However with runtime
typechecking, if a function passes the tests, we have the
certainty that no type error will be the cause for failure
when executing that function.

** Bibliography

- **[Moor]**
  Oege De Moor, Kevin Backhouse, S. Doaitse Swierstra,
  /First-class Attribute Grammars/,
  Informatica, 2000.

- **[Viera]**
  Marcos Viera, Swierstra, S. Doaitse Swierstra, Wouter Swierstra,
  /Attribute Grammars Fly First-class: How to Do Aspect Oriented Programming in Haskell/,
  ICFP 2009.

- **[Balestrieri]**
  Florent Balestrieri,
  /The productivity of polymorphic stream equations and the composition of circular traversals/,
  University of Nottingham, 2015.

** Dependencies
ghc-8.0.1
mtl-2.2.1

** TODO
- Add locations to errors
- Pretty printer for errors
- Template haskell to generate grammar, bindings, gramDesc
- Reorganise source code for a better presentation (easier to read an understand).
- Longer, real-world examples
- Performance comparison with UUAG

* Header
** GHC Extensions

> {-# LANGUAGE
>       TypeOperators
>     , GADTs
>     , ExistentialQuantification
>     , DeriveDataTypeable
>     , GeneralizedNewtypeDeriving
>     , StandaloneDeriving
>  #-}

** Module Exports

- when using the library primitives, the user should never
  SEE any `Dynamic', always concrete types.
- the user should never SEE Attribute, only `Attr k a'

> module AG where

** Module Imports

> import Prelude hiding (all, sequence)
> import Control.Applicative
> import Control.Monad.Except hiding (sequence)
> import Control.Monad.Trans.Except (except)
> import Control.Monad.Writer.Strict hiding (sequence)
> import Control.Monad.Reader hiding (sequence)
> import Data.Maybe (fromMaybe)
> import Data.List (nub, (\\))
> import Data.Dynamic
> import Data.Function (on)
> import qualified Data.Set as Set
> import Data.Set (Set)
> import qualified Data.Map as Map
> import Data.Map (Map)
> import Data.Traversable
> import Data.Foldable (foldMap, all)
> --import GHC.Stack -- callstacks
> import Unknown

* General definitions
** Function composition

> cst2 r x y = r
> cst3 r x y z = r
> res2 g f x y = g (f x y)
> res3 g f x y z = g (f x y z)

** Maybe, Either

> filterJust xs = [ x | Just x <- xs ]
> justLeft (Left x) = Just x
> justLeft _ = Nothing

** List

> is_set :: Eq a => [a] -> Bool
> is_set l = nub l == l

> duplicates :: Eq a => [a] -> [a]
> duplicates l = l \\ nub l

** String operations (over ShowS)

> str s = (s ++)

** Set and Map operations

> infixr 1 :->
> type (:->) = Map

> infixr 2 |->, |-
> (|->) = Map.singleton

Nicer pairs for association lists [(a,b)]

> x |- y = (x,y)

Type of binary operators

> type Op a = a -> a -> a

> infixr 1 \/
> (\/) :: Ord k => Op (k :-> a)
> (\/) = Map.union

> infixr 1 <+>
> (<+>) :: Monoid a => Op a
> (<+>) = mappend

Pointwise application for finite maps.
The result is defined on the intersection of the arguments.
Since we cannot define pure, (what would the domain be?)
then it's not an applicative instance.

> applyMap :: Ord k => Map k (a -> b) -> Map k a -> Map k b
> applyMap = Map.intersectionWith ($)

Set operations

> unionSets :: Ord b => (a -> Set b) -> Set a -> Set b
> unionSets = foldMap

** Dynamics

> toDynP :: Typeable a => proxy a -> a -> Dynamic
> toDynP _ = toDyn

* Context free grammar

An attribute grammar has two elements: a context free grammar
describing a language, or equivalently, the type of its parse
tree.  And semantic rules, that define the value of
attributes for each non-terminal of the grammar, (each node
of the tree).

** Tree
We start by defining a general tree type. The tree is parameterised with
node labels, which are simply the production in the case of the input tree,
but can also be paired with attributes in the case of a decorated tree.
The `AttrMap' field introduces the non-terminal data.

> data Tree n = Node n (Child :-> Tree n) AttrMap
>             deriving Show
> type InputTree = Tree Production
> type DecoratedTree = Tree (Production, AttrMap)


** Grammar basic blocks
*** Names

> type Name = String
> type NonTerminalName = Name
> type ProdName = (NonTerminal, Name)
> type ChildName = (Production, Name)
> type AttrName = Name

*** Non-terminals

> newtype NonTerminal = NT NonTerminalName deriving (Eq, Ord)

*** Production

> data Production = Production
>   { prod_name :: ProdName
>   , prod_orphans :: [Orphan]
>   , prod_terminals :: Set (AttrOf T) }
>   deriving (Eq, Ord)

*** Children

> data Child = Child
>   { child_name :: ChildName
>   , child_nt ::  NonTerminal }
>   deriving (Eq, Ord)

> type Orphan = (Name, NonTerminal)

> type Children = [Child]

*** Terminals
`Terminals' is abstract so that the user doesn't manipulate
`AttrOf'.

> newtype Terminals = Terminals {terms_set :: Set (AttrOf T)}

> nilT :: Terminals
> nilT = Terminals Set.empty
> consT :: Typeable a => Attr T a -> Terminals -> Terminals
> consT t (Terminals ts) =
>   Terminals $ Set.insert (AttrOf t) ts

*** Misc functions

> prod_child :: Production -> Orphan -> Child
> prod_child p (c,n) = Child (p,c) n

> prod_children :: Production -> Children
> prod_children p = map (prod_child p) $ prod_orphans p

> orphan :: Child -> Orphan
> orphan c = (snd (child_name c), child_nt c)
> orphans = map orphan

*** Show instances

The show instances display the non-qualified names.  This
might lead to misunderstanding in case homonymes are defined.

> instance Show NonTerminal where
>   show (NT n) = n
> instance Show Production where
>   show = snd . prod_name

> instance Show Child where
>   show = snd . child_name

*** Public constructors

> non_terminal = NT

Remark: if the children are built with a different
production, then the production that we create will have
distinct children (new ones with the same short name but
different fully qualified name).

> production ::
>   NonTerminal -> Name -> Children -> Terminals -> Production
> production n p cs (Terminals ts) =
>   Production (n,p) (orphans cs) ts

> child :: Production -> Name -> NonTerminal -> Child
> child p c n = Child (p, c) n

> prod_nt = fst . prod_name
> child_prod = fst . child_name

** DSL for creating the grammar
*** Datatypes for the DSL

> infix 1 ::=
> infixr 2 :|
> infix 3 :@
> infix 1 :::
> infix 4 :&

> type GrammarSpec = [NTSpec Name Name ChildTermSpec]
> data NTSpec n p c =
>   n ::= ProdSpecs p c

> data ProdSpecs p c
>   = p :@ c
>   | ProdSpecs p c :| ProdSpecs p c

> data ChildSpec = Name ::: NonTerminal

> type ChildrenSpec = [ChildSpec]

> data ChildTermSpec = ChildrenSpec :& Terminals

*** Semantics: building a grammar

Building each element of the grammar. Typically we bind the result
in a pattern binding that has the same shape as the specification.
See Examples.lhs.

> grammar ::
>   GrammarSpec -> [NTSpec NonTerminal Production Children]
> grammar = map nt_spec
>   where
>     nt_spec (name ::= prods) =
>       let nt = non_terminal name in (nt ::= prod_spec nt prods)

private

> prod_spec nt (name :@ children :& ts) = prod :@ cs
>   where
>     prod = production nt name cs ts
>     cs = map child_spec children
>     child_spec (name ::: nt) =
>       child prod name nt

> prod_spec nt (p :| p') =
>   prod_spec nt p :| prod_spec nt p'

production can be used to extend a non-terminal

> productions ::
>   NTSpec NonTerminal Name ChildTermSpec ->
>   ProdSpecs Production Children
> productions (nt ::= prods) = prod_spec nt prods

** Grammar

A grammar can be given by a set of production.  This fully
specifies a grammar, and the representation is unique.  (up
to set equality).

Note: should we make this a new type?
It might be nice for type inference, and error messages.
It doesn't need to be abstract.

> type Grammar = Set Production

Some values are not valid grammars: we must check that the
orphans and terminals have unique names for each production.

> valid_grammar :: Grammar -> Bool
> valid_grammar = all valid_production

Children of a production must have unique names.
Note: if two terminals have the same name but different types
then they are different: only their names are overloaded.

TODO: explicit error (which ones are duplicated?)

> valid_production :: Production -> Bool
> valid_production p = is_set cs
>   where cs = map fst $ prod_orphans p

> gram_children :: Grammar -> Set Child
> gram_children gram =
>   Set.foldr
>     (\cs -> Set.union (Set.fromList cs))
>     Set.empty
>     (Set.map prod_children gram)

** Attributes

*** Attribute kinds: I, S, T

> data I -- inherited
> data S -- synthesized
> data T -- terminal

> data Kind k where
>   I :: Kind I
>   S :: Kind S
>   T :: Kind T

> instance Eq (Kind k) where
>   (==) = cst2 True -- singleton type
> instance Ord (Kind k) where
>   compare = cst2 EQ
> instance Show (Kind k) where
>   showsPrec _ I = ('I' :)
>   showsPrec _ S = ('S' :)
>   showsPrec _ T = ('T' :)

**** Eq, Ord

> eqKind :: Kind j -> Kind k -> Bool
> eqKind I I = True
> eqKind S S = True
> eqKind T T = True
> eqKind _ _ = False

> compareKind :: Kind j -> Kind k -> Ordering
> compareKind j k | eqKind j k = EQ
> compareKind I _ = LT
> compareKind T _ = GT
> compareKind j k = dualOrdering $ compareKind k j

> dualOrdering LT = GT
> dualOrdering GT = LT
> dualOrdering EQ = EQ

*** Attr, AttrOf, Attribute

> data Attr k a = Attr
>   { attr_name :: Name
>   , attr_kind :: Kind k}

> attr :: Typeable a => Name -> Kind m -> p a -> Attr m a
> attr n k _ = Attr n k

> data AttrOf k where
>   AttrOf :: Typeable a => Attr k a -> AttrOf k

> data Attribute where
>   Attribute :: Typeable a => Attr k a -> Attribute

**** Eq, Ord
WARNING: what if two attributes with the same name and
different types are used? If we consider them equal then the
value associated to the name could change type.  If we
consider them different then it should behave just fine.  The
names are overloaded but we can distinguish the concrete
attributes by their types.

> instance Eq Attribute where
>   x == y  =  compare x y == EQ

> instance Ord Attribute where
>   Attribute a@(Attr x j) `compare` Attribute b@(Attr y k) =
>     (x `compare` y)
>     `lexicographic` ((j `compareKind` k)
>                      `lexicographic` (typeRep a `compare` typeRep b))

> lexicographic EQ c = c
> lexicographic c _ = c

> eqAttr :: (Typeable a, Typeable a') =>
>   Attr k a -> Attr k' a' -> Bool
> eqAttr x y =
>   Attribute x == Attribute y

> compareAttr :: (Typeable a, Typeable a') =>
>   Attr k a -> Attr k' a' -> Ordering
> compareAttr x y =
>   Attribute x `compare` Attribute y

> instance Eq (AttrOf k) where
>   x == y  = compare x y == EQ
> instance Ord (AttrOf k) where
>   AttrOf x `compare` AttrOf y =
>     x `compareAttr` y

> instance Typeable a => Show (Attr k a) where
>   show = attr_name

> instance Show Attribute where
>   show (Attribute x) = show x

> instance Show (AttrOf k) where
>   show (AttrOf x) = show x


*** Attributions
An attribution is a finite map from attribute name to values.
Note: the use of Dynamics prevents us from having polymorphic
attributes.

> type AttrMap = Attribute :-> Dynamic
> emptyAttrs :: AttrMap
> emptyAttrs = Map.empty
> mergeAttrs :: Op AttrMap
> mergeAttrs = Map.union

Note: we do an unsafe conversion, because lookupAttr will
only be called after the AG has been typechecked at runtime.

> lookupAttr :: (Typeable a) => Attr k a -> AttrMap -> Maybe a
> lookupAttr a m =
>   (\d -> fromDyn d (err d))
>   <$> Map.lookup (Attribute a) m
>   where
>     err d = error $ "[BUG] lookupAttr:" ++ attr_type_err a d

> attr_type_err a d = "attribute " ++ show a
>             ++ ", expected type: " ++ show (typeRep a)
>             ++ ", runtime type: " ++ show (dynTypeRep d)

> projAttr :: Typeable a => AttrMap -> Attr k a -> Maybe a
> projAttr = flip lookupAttr
> (|=>) :: Typeable a => Attr k a -> a -> AttrMap
> a |=> x = Attribute a |-> toDyn x

**** Parent, children and terminal attributions.

> type TerminalAttrs = AttrMap
> type ParentAttrs = AttrMap
> type ChildrenAttrs = Child :-> AttrMap
> emptyChildrenAttrs :: ChildrenAttrs
> emptyChildrenAttrs = Map.empty
> mergeChildrenAttrs :: Op ChildrenAttrs
> mergeChildrenAttrs x y =
>   Map.unionWith mergeAttrs x y

**** Family of attribution

Attributions for the parent of the node, for the children and
the terminals.  (Not all children need to be given an
attribute).  Families are used as input and output of rules,
however the terminal attributes are only used
as input. In the output, the terminal map will always be
empty.

> data Family = Family
>   { parentAttrs :: ParentAttrs
>   , childrenAttrs :: ChildrenAttrs
>   , terminalAttrs :: TerminalAttrs
>   }

> emptyFam :: Family
> emptyFam =
>   Family emptyAttrs emptyChildrenAttrs emptyAttrs

> mergeFam :: Op Family
> mergeFam (Family x xs a) (Family y ys b) =
>   Family (mergeAttrs x y)
>          (mergeChildrenAttrs xs ys)
>          (mergeAttrs a b)

* Rules
An attribute grammar is given by a context free grammars and
attribution rules.

 > type AG = (Grammar, Rule)

In order to check that the rules are compatible with a
grammar, we must collect information about the rules:

Which attributes are used and with which type from the
parent, the children, or the terminal data..

To capture this information we will use monads.

In order to gather information from the use of input family, we
must define rule in a specific monad in which the input family
is accessed through primitives.

> newtype R a = R {runR :: Reader Family a} -- the rule monad
>   deriving (Functor, Applicative, Monad, MonadReader Family)

In order to compute rules, we must first check that they are
valid.  Rules are defined in the context of a production, and
may fail if some constraints are not met, like using a child
that is not a valid child of the current production. Or an
attribute with the wrong type.
And lastly, we collect constraints.

> newtype A a = A (ReaderT Production (ExceptT Error (Writer Context)) a) -- the aspect monad
>   deriving (Functor, Applicative, Monad, MonadReader Production, MonadError Error, MonadWriter Context)

private

> runA :: A a -> Production -> (AG a, Context)
> runA (A a) p =
>   ag . runWriter . runExceptT $ runReaderT a p
>   where
>     ag (e, c) = (except e, c)

> current_production :: A Production
> current_production = ask

A, R and AR are abstract. (R is even private)

> newtype AR a = AR {runAR :: A (R a)}
>
> instance Applicative AR where
>   pure x = AR (pure (pure x))
>   AR f <*> AR x = AR ((<*>) <$> f <*> x)
> instance Functor AR where
>   fmap f x = pure f <*> x

Most operations for the user are in AR which is not a monad
but an Applicative. Some of them are in the A monad (and none
are in R). In order to use them, we should use the following
specialised bind and join operators.

> joinAR :: A (AR a) -> AR a
> joinAR x = AR $ join (runAR <$> x)

> bindAR :: A a -> (a -> AR b) -> AR b
> bindAR x f = joinAR (f <$> x)

> bindAR_ :: A () -> AR a -> AR a
> bindAR_ x y = x `bindAR` const y

A rule takes an inherited attribution for the parents, and
synthesized attributions for the children and compute a
synthesized attribution for the parents and inherited
attributions for the children.

Rule is abstract, only operations are the monoid, and computing the context.

> newtype Rule = Rule (AR Family)
> inRule2 f (Rule x) (Rule y) = Rule (f x y)

> emptyRule :: Rule
> emptyRule = Rule $ pure emptyFam

> mergeRule :: Op Rule
> mergeRule = inRule2 $ liftA2 mergeFam

> instance Monoid Rule where
>   mempty = emptyRule
>   mappend = mergeRule

> (&) = mergeRule

> concatRules :: [Rule] -> Rule
> concatRules = mconcat

`runRule` is PRIVATE

> type FamRule = Family -> Family

> runRule :: Rule -> (AG FamRule, Context)
> runRule (Rule (AR a)) = runA b p
>   where b = liftM (runReader . runR) a
>         p = error "context: assert false"

Note: the production in the readerT is not used for rules.
Because when we build rules we always override the production with
a call to `local' (see the code of `inh' and `syn').

> context :: Rule -> Context
> context = snd . runRule

> check_rule :: Rule -> Maybe Error
> check_rule = justLeft . runExcept . fst . runRule

** Aspects

> newtype Aspect = Aspect (Production :-> Rule)
> inAspect2 f (Aspect x) (Aspect y) = Aspect (f x y)
> emptyAspect = Aspect $ Map.empty
> mergeAspect :: Op Aspect
> mergeAspect = inAspect2 $ Map.unionWith mergeRule

> instance Monoid Aspect where
>   mempty = emptyAspect
>   mappend = mergeAspect

> concatAspects :: [Aspect] -> Aspect
> concatAspects = mconcat

* Error datatype

> data Error
>   = Error_Rule_Invalid_Child Child Production
>   | Error_Rule_Missing Missing  -- raised when checking rules with a grammar
>   | Error_InhDesc_Duplicate [AttrOf I] -- raised when checking InhDesc
>   | Error_InhDesc_Missing (Set Require_I) -- raised when checking InhDesc and rules
>   | Error_SynDesc_Missing (Set Ensure_S) -- raised when checking SynDesc, Grammar and rules
>   | Error_ProdDesc_Duplicate_Children [Child] Production
>   | Error_ProdDesc_Invalid_Children (Set Child) Production
>   | Error_ProdDesc_Missing_Children (Set Child) Production
>   | Error_ProdDesc_Duplicate_Terminals [AttrOf T]
>   | Error_ProdDesc_Invalid_Terminals (Set (AttrOf T)) Production
>   | Error_ProdDesc_Missing_Terminals (Set (AttrOf T)) Production
>   | Error_NtDesc_Duplicate_Productions [Production] NonTerminal
>   | Error_NtDesc_Invalid_Productions (Set Production) NonTerminal
>   | Error_GramDesc_Duplicate NonTerminal
>   | Error_GramDesc_Missing (Set NonTerminal)
>   | Error_GramDesc_Wrong_Types (Set Child)
>   | Error_Missing Missing
>   deriving Show

 - `Error_Rule_Invalid_Child c p' ::
     When child `c' was used in the context of the production
     `p` which doesn't list this child. This error coms from
     a rule that projects attribute from a wrong child.

* Contexts, Constraints

While building attribution rules, we build a rule of
inference in parallel that we call `Context` here. The
context is formed of a set of premises and a set of
conclusions. The meaning of the context is that the
conjunction of premises entails the conjunction of
conclusions. The premises are captured by the datatype
`Require` and the conclusion by the datatype `Ensure`.

When the rule set is deemed complete, we can check its
context with respect to a grammar.

Note that the use of the kind and the phantom type on
Attributes ensures that attributes can only be used with
their given kind and type. Therefore we do not need to check
attribute types. And the use of children lists in production
ensures that children can only be used in their given
production.

Therefore we only need to keep track of attributes that are
used (required) and attributes that are defined (ensured).

** Constraints

> data Constraint k t where
>   Constraint :: Typeable a =>
>     Attr k a -> t -> Constraint k t

> constr_obj :: Constraint k t -> t
> constr_obj (Constraint a x) = x
> constr_attr :: Constraint k t -> AttrOf k
> constr_attr (Constraint a x) = AttrOf a

> instance Eq t => Eq (Constraint k t) where
>   Constraint a x == Constraint b y =
>     a `eqAttr` b && x == y

> instance Ord t => Ord (Constraint k t) where
>   compare (Constraint a x) (Constraint b y)
>     = lexicographic (compareAttr a b) (compare x y)
> instance Show t => Show (Constraint k t) where
>   showsPrec _ (Constraint a x) = shows a . str "#" . shows x

> instance Functor (Constraint k) where
>   fmap f (Constraint a x) =
>     Constraint a (f x)

** Contexts
Contexts are modelled with sets of premises and
conclusions. They form a monoid, therefore the Writer monad
uses the mappend function to update the constraints. Note
that contexts are cannot be more simplified.
Each conclusion is participating in proving one premise.

Ensure_I and Ensure_S are generated by rules.
Ensure_T are generated by the grammar definition.

> type Ensure_I = Constraint I Child
> type Ensure_S = Constraint S Production
> type Ensure_T = Constraint T Production

> type Require_I = Constraint I NonTerminal
> type Require_S = Constraint S NonTerminal
> type Require_T = Constraint T Production

> data Context = Ctx
>   { ensure_I  :: Set Ensure_I
>   , ensure_S  :: Set Ensure_S
>   , require_I :: Set Require_I
>   , require_S :: Set Require_S
>   , require_T :: Set Require_T
>   }
>   deriving Show

> emptyCtx :: Context
> emptyCtx = Ctx Set.empty Set.empty Set.empty Set.empty Set.empty

> mergeCtx :: Op Context
> mergeCtx (Ctx ec ep rc rp rt) (Ctx ec' ep' rc' rp' rt') =
>   Ctx (Set.union ec ec')
>       (Set.union ep ep')
>       (Set.union rc rc')
>       (Set.union rp rp')
>       (Set.union rt rt')

> instance Monoid Context where
>   mempty = emptyCtx
>   mappend = mergeCtx

Extract all the terminals axioms from a grammar.

> ensure_T :: Grammar -> Set Ensure_T
> ensure_T = unionSets prod_ensure_T

> prod_ensure_T :: Production -> Set Ensure_T
> prod_ensure_T p = Set.map ensure $ prod_terminals p
>   where
>     ensure (AttrOf a) = Constraint a p

** Checking contexts
There is no invalid context, and no redundent
constraints. The only thing we can do is to check whether a
context is complete: i.e. all `require` constraints are met
by matching `ensure` constraints, and all terminals are
defined in the grammar.

> complete ::
>   Grammar -> Context -> Bool
> complete = nullMissing `res2` missing

*** Missing rules
The missing `ensure` constraints for the rules to be complete.

> type Missing = (Set Ensure_I, Set Ensure_S, Set Ensure_T)
> nullMissing (x,y,z) = Set.null x && Set.null y && Set.null z

> missing ::
>   Grammar -> Context -> Missing
> missing g c =
>   ( unionSets (missing_I (gram_children g) (ensure_I c)) (require_I c)
>   , unionSets (missing_S g (ensure_S c)) (require_S c)
>   , missing_T (ensure_T g) (require_T c))

> missing_I :: Set Child -> Set Ensure_I -> Require_I -> Set Ensure_I
> missing_I children ensure r@(Constraint a n) =
>   Set.difference match_children match_ensure
>   where
>     match_children =
>       Set.map (<$ r)
>        $ Set.filter ((== n) . child_nt) children
>     match_ensure =
>       Set.filter ((== r) . fmap child_nt) ensure

> missing_S :: Set Production -> Set Ensure_S -> Require_S -> Set Ensure_S
> missing_S prods ensure r@(Constraint a n) =
>   Set.difference match_prods match_ensure
>   where
>     match_prods =
>       Set.map (<$ r)
>        $ Set.filter ((== n) . prod_nt) prods
>     match_ensure =
>       Set.filter ((== r) . fmap prod_nt) ensure

This case is different from S, and I since the terminal
attributes are not associated with non-terminals but with
productions.

> missing_T :: Set Ensure_T -> Set Require_T -> Set Ensure_T
> missing_T = flip Set.difference

** Context primitives
The primitive ways to update the context are through the
require_* and ensure_* functions given below.

> tell_parent f =
>   current_production >>= tell . f

Generate errors if the child is not valid in the current production.

> assert_child c = do
>   p <- current_production
>   unless (c `elem` prod_children p)
>     $ throwError (Error_Rule_Invalid_Child c p)

> cstr :: Typeable a =>
>   Attr k a -> t -> Set (Constraint k t)
> cstr a x =
>   Set.singleton (Constraint a x)

> require_child ::
>   Typeable a => Child -> Attr S a -> A ()
> require_child c a = do
>   assert_child c
>   tell $ emptyCtx { require_S = cstr a (child_nt c) }

> ensure_child ::
>   Typeable a => Child -> Attr I a -> A ()
> ensure_child c a = do
>   assert_child c
>   tell $ emptyCtx { ensure_I = cstr a c }

> require_parent ::
>   Typeable a => Attr I a -> A ()
> require_parent a = tell_parent $ \p ->
>   emptyCtx { require_I = cstr a (prod_nt p) }

> ensure_parent ::
>   Typeable a => Attr S a -> A ()
> ensure_parent a = tell_parent $ \p ->
>   emptyCtx { ensure_S = cstr a p }

> require_terminal ::
>   Typeable a => Attr T a -> A ()
> require_terminal a = tell_parent $ \p ->
>   emptyCtx { require_T = cstr a p }

* Rule primitives
Rules are defined in an applicative `AR', that comes with
primitives to project attributes from either the parent, a
child of the production or the terminal child.  Those
primitive generate `Require' constraints.

The `Maybe' versions of `chi', `par' and `ter' do not add any
constraints: their success or failure is captured by the
Maybe monad at runtime.

Children attribute

> (?), chiM :: Typeable a => Child -> Attr S a -> AR (Maybe a)
> (?) c a = AR $ return $ do
>   cs <- asks childrenAttrs
>   return $ lookupAttr a =<< Map.lookup c cs

> chiM = (?)

Parent attribute

> parM :: Typeable a => Attr I a -> AR (Maybe a)
> parM a = AR $ return $ do
>  lookupAttr a <$> asks parentAttrs
>

Terminal attribute

> terM :: Typeable a => Attr T a -> AR (Maybe a)
> terM a = AR $ return $ do
>   lookupAttr a <$> asks terminalAttrs

The strict versions are all instances of the following
function, which adds a constraint before safely forcing the
evaluation of the attribute.

> strictProj :: Typeable a =>
>   (Attr k a -> AR (Maybe a)) ->   -- the maybe operation
>   (Attr k a -> A ()) ->           -- the constraint
>   Attr k a -> AR a
> strictProj get require a = AR $ do
>   require a
>   rma <- runAR (get a)
>   return (fromMaybe err <$> rma) -- safe coercion after we added the constraint
>   where
>     err = error $ "[BUG] strictProj: undefined attribute " ++ show a

> infix 9 !
> (!), chi :: Typeable a => Child -> Attr S a -> AR a
> (!) c = strictProj (c ?) (require_child c)
> chi = (!)

> par :: Typeable a => Attr I a -> AR a
> par = strictProj parM require_parent

> ter :: Typeable a => Attr T a -> AR a
> ter = strictProj terM require_terminal

(private) Common boiler plate to build a rule (shared by inh and syn)

> build_rule :: Typeable a =>
>   Attr k a ->
>   Production ->
>   A () ->
>   (AttrMap -> Family) ->
>   AR a -> Rule
> build_rule a p c f r = Rule $ AR $ do
>    r' <- local (const p) (c >> runAR r)
>    return $ fam <$> r'
>   where
>     fam x = f (Attribute a |-> toDyn x)


Inherited attributes are defined for a specific child of a
production.  The production is determined by the Child.

NOTE: since the child_prod is ProdName instead of a Production,
we need to add a Production as an argument.

> inh :: Typeable a => Attr I a -> Child -> AR a -> Rule
> inh a c = build_rule a (child_prod c) (ensure_child c a)
>   $ \attrs -> emptyFam { childrenAttrs = c |-> attrs }

> inhs :: Typeable a => Attr I a -> [(Child, AR a)] -> Rule
> inhs a = foldl (\rs (c,r) -> rs & inh a c r) emptyRule

Synthesized attributes are defined for the parent of a production.

> syn :: Typeable a => Attr S a -> Production -> AR a -> Rule
> syn a p = build_rule a p (ensure_parent a)
>   $ \attrs -> emptyFam { parentAttrs = attrs }

> syns :: Typeable a => Attr S a -> [(Production, AR a)] -> Rule
> syns a = foldl (\rs (p,r) -> rs & syn a p r) emptyRule

* Other primitives (access context)

The current production

> prod :: A Production
> prod = ask

The children of the current production

> children :: A Children
> children = asks prod_children

The parent non-terminal of the current production

> parent :: A NonTerminal
> parent = asks prod_nt

* Generic rules

Note that all those rules are in only using the public
primitives and could be defined by the user.

`copy' copies the attribute the parent to the child.

> copy :: Typeable a => Attr I a -> Child -> Rule
> copy a c = inh a c (par a)

> copyN :: Typeable a => Attr I a -> Children -> Rule
> copyN a cs = concatRules . map (copy a) $ cs

`copyP' copies the inherited attribute of the parent to all
the children that have the same non-terminal.

> copyP :: Typeable a => Attr I a -> Production -> Rule
> copyP a p = copyN a cs
>   where cs = [ c | c <- prod_children p
>                  , child_nt c == prod_nt p ]

`copyG' implements the copy rule systematically for a whole
grammar.

> copyG :: Typeable a => Attr I a -> Grammar -> Rule
> copyG a = Set.foldr (\p r -> copyP a p & r) emptyRule

`copyGN' only implements the copy rule for the given
nonterminal, but applies it to all the productions in the grammar.

> copyGN :: Typeable a => Attr I a -> NonTerminal -> Grammar -> Rule
> copyGN a n g = copyG a $ Set.filter (\p -> prod_nt p == n) g

`collect' applies a function to the attributes of a list of children
to compute a synthesized attribute.

> collect :: Typeable a => Attr S a -> ([a] -> a) -> Production -> Children -> Rule
> collect a reduce p cs = syn a p $
>   reduce <$> traverse (!a) cs

`collectAll' applies the function to all the attributes for
all children that implement it.

> collectAll :: Typeable a => Attr S a -> ([a] -> a) -> Production -> Rule
> collectAll a reduce p = syn a p $
>   children `bindAR` \cs ->
>   (reduce . filterJust) <$> traverse (?a) cs

`collectP' applies the function to the attributes of all the
children that have the same non-terminal as the parent.
By hypothesis, we know that the attribute will be defined for them.

> collectP :: Typeable a => Attr S a -> ([a] -> a) -> Production -> Rule
> collectP a reduce p = syn a p $
>   children `bindAR` \cs ->
>   parent `bindAR` \nt ->
>   let cs' = [ c | c <- cs, child_nt c == nt ] in
>   (reduce . filterJust) <$> traverse (?a) cs

* Running the grammar
** Specifying input and output
Rather than run the AG on the general tree type.

 > type Partial a = Either Error a -- success or failure monad

 > check :: spec t i s -> Rule -> Partial (AG t i s)
 > run :: AG t i s -> t -> i -> s

we must build (total) conversions between
- t and the tree type,
- i,s and the AttrMap type.

To specify i and s, we must keep track of the attributes that
they will be using and build conversion functions
(i -> AttrMap) and (AttrMap -> s).

*** Synthesized attributes
For the synthesized attributes the following interface is enough.

SynDesc is abstract

> newtype SynDesc s = SynDesc { runSynDesc ::
>   Writer (Set (AttrOf S)) (AttrMap -> s) }

> instance Functor SynDesc where
>   fmap f x = pure f <*> x

> instance Applicative SynDesc where
>   pure x = SynDesc $ return $ pure x
>   SynDesc f <*> SynDesc x =
>     SynDesc $ liftM2 (<*>) f x

> project :: Typeable a => Attr S a -> SynDesc a
> project a = SynDesc $ do
>   tell (Set.singleton (AttrOf a))
>   return $ fromMaybe err . lookupAttr a
>  where
>    err = error $ "[BUG] project: undefined attribute " ++ show a

**** Private

> proj_S :: SynDesc s -> AttrMap -> s
> proj_S = fst . runWriter . runSynDesc


*** Inherited attributes
Describing the root's inherited attribute and the terminals
of a production follow a same pattern, therefore the
functions are generalised over the kind of attributes and
will be instanciated with `I' or `T' depending on the case.

> newtype AttrDesc k t  = AttrDesc { runAttrDesc ::
>    Writer ([AttrOf k]) (t -> AttrMap) }

> type InhDesc = AttrDesc I
> type TermDesc = AttrDesc T

> emptyAttrDesc :: AttrDesc k t
> emptyAttrDesc = AttrDesc $ return $ pure $ Map.empty

> embed_I :: Typeable a =>
>   Attr I a -> (i -> a) -> InhDesc i
> embed_I a p = embed_dyn a (toDyn . p)

> embed_T :: Typeable a =>
>   Attr T a -> (t -> Maybe a) -> TermDesc t
> embed_T a p = embed_dyn a (toDyn . (fromMaybe <*> err) . p)
>   where err = error $ "[BUG] embed_T: match error to compute terminal: " ++ show a

> (#) :: AttrDesc k t -> AttrDesc k t -> AttrDesc k t
> AttrDesc x # AttrDesc y =
>   AttrDesc $ liftA2 union x y
>  where
>    union f g = \x -> Map.union (f x) (g x)

**** Private

> embed_dyn :: Typeable a =>
>   Attr k a -> (t -> Dynamic) -> AttrDesc k t
> embed_dyn a p = AttrDesc $ do
>   tell [AttrOf a]
>   return $ Map.singleton (Attribute a) . p

> runInhDesc = runAttrDesc
> runTermDesc = runAttrDesc

> proj_I :: InhDesc i -> i -> AttrMap
> proj_I = fst . runWriter . runInhDesc

*** Example

  #+BEGIN_SRC haskell
data I = I { a :: Int, b :: Bool }
data S = S { c :: String, d :: Float }

count  :: Attr Int
flag   :: Attr Bool
output :: Attr String
speed  :: Attr Float

specI = embed count a # embed flag b :: InhDesc I
specS = S <$> project output <*> project speed :: SynDesc S
  #+END_SRC

** Concrete tree specification

In order to run the AG in a type-safe way, we must check that
a concrete type is compatible the context free grammar. We do
this verification at runtime, but once and for all.

Since we run the grammar on a general tree type, we must
convert a concrete type into the general tree. This
conversion is given by the user. The library offers
primitives for building the conversion and at the same time
a context free grammar is computed.

The conversion is given in small blocks: We first ask
functions computing children of a production, those functions
are combined in productions, and the productions are combined
to represent a family of types.

If the conversion is not compatible with the grammar, for
instance if the children do not correspond to a given
production, etc.  then a runtime error is thrown.
The idea is that the programmer should really know what he's doing:
just like when using `tail'.

*** ChildDesc
`ChildDesc t' is an abstract type for describing the children
of type `t'.

> data ChildDesc t = ChildDesc
>   { childDesc_child :: Child
>   , childDesc_type :: TypeRep -- representation of the child's type
>   , childDesc_proj :: t -> Maybe (Child, Dynamic) }

`childDesc' describes a child: the user provides a partial
function to extract the child. The function typically does
a pattern matching which is the reason it might fail.

> childDesc :: (Typeable a, Typeable b) =>
>   Child -> (a -> Maybe b) -> ChildDesc a

> childDesc c p = ChildDesc c ty  p'
>   where
>     ty = typeRep (proxy p)
>     p' x = (\y -> (c, toDyn y)) <$> p x
>     proxy :: (a -> Maybe b) -> Proxy b
>     proxy _ = Proxy

*** ProdDesc

`ProdDesc a' describes a constructor of the type `a' (viewed
as a grammar production).

> newtype ProdDesc t = ProdDesc { runProdDesc ::
>   AG (ProdDescRec t) }

> data ProdDescRec t = ProdDescRec
>   { prodDesc_prod :: Production
>   , prodDesc_children_types :: Child :-> TypeRep
>   , prodDesc_match :: t -> Maybe (Child :-> Dynamic, AttrMap) }

`prodDesc' associates a production to a constructor.

- the children must be children of the production.
- all the production's children are provided
- all the production's terminals are provided

Note: No error is raised if the termDesc produces more
terminals than the production needs.  we will just ignore
them.

> prodDesc :: (Typeable a) =>
>   Production -> [ChildDesc a] -> TermDesc a -> ProdDesc a
> prodDesc prod cds ts = ProdDesc $ this
>  where
>  this
>   | not (null duplicate_children) =
>       throwError $ Error_ProdDesc_Duplicate_Children duplicate_children prod
>   | not (Set.null invalid_children) =
>       throwError $ Error_ProdDesc_Invalid_Children invalid_children prod
>   | not (Set.null missing_children) =
>       throwError $ Error_ProdDesc_Missing_Children missing_children prod
>   | not (Set.null invalid_terminals) =
>       throwError $ Error_ProdDesc_Invalid_Terminals invalid_terminals prod
>   | not (Set.null missing_terminals) =
>       throwError $ Error_ProdDesc_Missing_Terminals missing_terminals prod
>   | otherwise = do
>       check_attr_unique Error_ProdDesc_Duplicate_Terminals ts
>       return $ ProdDescRec prod children_types match
>   where
>     match = liftA2 (liftA2 (,)) child_proj (Just . term_proj)
>     children_types = Map.fromList $ child_type <$> cds
>     child_type c = (childDesc_child c, childDesc_type c)
>     child_proj = fmap Map.fromList . sequence . traverse childDesc_proj cds
>     (term_proj, term_attrs) = runWriter . runTermDesc $ ts
>     -- Checking children
>     duplicate_children = duplicates cs
>     invalid_children = cs `diff` prod_children prod
>     missing_children = prod_children prod `diff` cs
>     cs = childDesc_child <$> cds
>     diff = Set.difference `on` Set.fromList
>     -- Checking terminals
>     prod_terms = prod_terminals prod
>     terms = Set.fromList term_attrs
>     invalid_terminals = Set.difference terms prod_terms
>     missing_terminals = Set.difference prod_terms terms

`check_attr_unique' is private, but used by `check_inh_unique' and
`prodDesc'.

> check_attr_unique ::
>   ([AttrOf k] -> Error) -> AttrDesc k t -> AG ()
> check_attr_unique err desc
>   | null xs' = return ()
>   | otherwise = throwError $ err xs'
>   where
>     (proj, xs) = runWriter . runAttrDesc $ desc
>     xs' = duplicates xs

*** NtDesc

`NtDesc a' associates a non-terminal to the datatype `a'

> newtype NtDesc t = NtDesc { runNtDesc ::
>   AG (NtDescRec t) }

> data NtDescRec t = NtDescRec
>   { ntDesc_nt :: NonTerminal
>   , ntDesc_prods :: Set Production
>   , ntDesc_children_types :: Child :-> TypeRep
>   , ntDesc_match :: t -> Match }

> data Match =
>   Match { math_prod :: Production -- we don't actually need it to run the AG.
>         , match_child :: Child :-> Dynamic
>         , match_terminals :: AttrMap }

- all productions must belong to the given non-terminal
- productions must be distincts

> ntDesc :: (Typeable a) =>
>   NonTerminal -> [ProdDesc a] -> NtDesc a
> ntDesc nonterm agps =
>   NtDesc $ this =<< sequence (runProdDesc <$> agps)
>  where
>   this :: [ProdDescRec a] -> AG (NtDescRec a)
>   this ps
>    | not (null duplicate_prods) =
>        throwError $ Error_NtDesc_Duplicate_Productions duplicate_prods nonterm
>    | not (Set.null invalid_prods) =
>        throwError $ Error_NtDesc_Invalid_Productions invalid_prods nonterm
>    | otherwise = return $ NtDescRec nonterm productions children_types (match ps)
>    where
>      productions = Set.fromList prodlist
>      children_types = Map.unions (prodDesc_children_types <$> ps)
>      -- Pattern matching function
>      match [] x = error "ntDesc: match failure due to incorrect gramDesc specification" -- (or bug from the library)
>      match (p:ps) x =
>        maybe (match ps x)
>              (\(cs, ts) -> Match (prodDesc_prod p) cs ts)
>          $ prodDesc_match p x
>      -- Checking the production
>      prodlist = prodDesc_prod <$> ps
>      duplicate_prods = duplicates prodlist
>      invalid_prods = Set.filter ((nonterm /=) . prod_nt) productions

*** GramDesc

`GramDesc a' associates a grammar to a family of types, where
`a' is associated to the start symbol of the grammar: the
root of the tree will have type `a'.

- The child_type map is used later to check that the
  non-terminal associated with each child corresponds with
  the typeRep associated with each `childDesc'.

> newtype GramDesc a = GramDesc { runGramDesc ::
>   AG (NonTerminal, Grammar, Child :-> TypeRep, GramMap) }

> type GramMap = NonTerminal :-> (TypeRep, Dynamic -> Match)

> gramDesc :: (Typeable a) =>
>   NtDesc a -> GramDesc a
> gramDesc n =
>   insert_nt n $ GramDesc $ return (undefined, Set.empty, Map.empty, Map.empty)

- `insert_nt': The non-terminal associated with the NtDesc must not be
  already in the GramDesc.

> insert_nt :: (Typeable a) =>
>   NtDesc a -> GramDesc b -> GramDesc a
> insert_nt ndesc gdesc = GramDesc $ do
>   n <- runNtDesc ndesc
>   (_, gram_prods, gram_children_types, gram_match) <- runGramDesc gdesc
>   let nt = ntDesc_nt n
>   when (nt `Map.member` gram_match)
>     $ throwError $ Error_GramDesc_Duplicate nt
>   let match = Map.insert nt (typeRep ndesc, nt_match n) gram_match
>   let children_types = Map.union (ntDesc_children_types n) gram_children_types
>   let grammar = Set.union (ntDesc_prods n) gram_prods
>   return (nt, grammar, children_types, match)

Private

> nt_match :: Typeable a => NtDescRec a -> Dynamic -> Match
> nt_match d x = ntDesc_match d $ fromDyn x err
>   where err = error $ "[BUG] nt_match: expected type: "
>               ++ show (typeRep d) ++ ", runtime type: "
>               ++ show (dynTypeRep x)

** Checking the AG

The AG monad

> type AG = Except Error

> runAG :: AG a -> Either Error a
> runAG = runExcept

Unique attributes

> check_inh_unique ::
>   InhDesc i -> AG ()
> check_inh_unique =
>   check_attr_unique Error_InhDesc_Duplicate

All the required inherited attributes have been specified for
the root.

> check_inh_required ::
>   InhDesc i -> NonTerminal -> Set Require_I -> AG ()
> check_inh_required desc root req
>   | Set.null missing = return ()
>   | otherwise = throwError $ Error_InhDesc_Missing missing
>   where
>     missing = Set.difference req' is'
>     req' = Set.filter ((root ==) . constr_obj) req
>     is' = Set.fromList (cstr <$> is)
>     cstr (AttrOf a) = Constraint a root
>     (proj, is) = runWriter . runInhDesc $ desc

All the synthesized attributes accessed from the root are
ensured by the rules.

> check_syn_ensured ::
>   SynDesc s -> Grammar -> NonTerminal -> Set Ensure_S -> AG ()
> check_syn_ensured desc prods root ens
>   | Set.null missing = return ()
>   | otherwise = throwError $ Error_SynDesc_Missing missing
>   where
>     missing = unionSets (missing_S prods ens) ss'
>     ss' = Set.map cstr ss
>     cstr (AttrOf a) = Constraint a root
>     (proj, ss) = runWriter . runSynDesc $ desc

The non-terminal associated with each child must correspond
with the typeRep associated with each `childDesc'.

> check_gramDesc ::
>   GramDesc a -> AG (NonTerminal, Grammar, GramMap)
> check_gramDesc (GramDesc g) = do
>   (nt, gram, ctypes, grammap) <- g
>   check_children_types ctypes grammap
>   return $ (nt, gram, grammap)

> check_children_types ::
>   Child :-> TypeRep -> GramMap -> AG ()
> check_children_types types gram
>   | not (Set.null missing) =
>       throwError $ Error_GramDesc_Missing missing
>   | not (Map.null wrong_types) =
>       throwError $ Error_GramDesc_Wrong_Types (Map.keysSet wrong_types)
>   | otherwise = return ()
>  where
>    (!) = (Map.!)
>    missing = Set.difference children_nt (Map.keysSet gram)
>    children_nt = child_nt `Set.map` Map.keysSet types
>    wrong_types = Map.filterWithKey wrong_type types
>    wrong_type c t = fst (gram ! child_nt c) /= t -- well-defined if Set.null missing

> check_grammar ::
>   Missing -> AG ()
> check_grammar missing
>   | not (nullMissing missing) = throwError $ Error_Missing missing
>   | otherwise = return ()

Check the whole AG.

> check ::
>   GramDesc t -> InhDesc i -> SynDesc s -> Rule -> AG (NonTerminal, FamRule, Coalg)
> check g i s r = do
>   (root, grammar, gmap) <- check_gramDesc g
>   let (check_rule, ctx) = runRule r
>   famrule <- check_rule
>   check_grammar (missing grammar ctx)
>   check_inh_unique i
>   check_inh_required i root (require_I ctx)
>   check_syn_ensured s grammar root (ensure_S ctx)
>   return (root, famrule, coalg gmap)

> run :: Typeable t =>
>   GramDesc t -> InhDesc i -> SynDesc s -> Rule -> AG (t -> i -> s)
> run g i s r = do
>   (root, famrule, coalg) <- check g i s r
>   let sem = sem_coalg (sem_prod famrule) coalg root . toDynP g
>   return $ \x -> proj_S s . sem x . proj_I i

> coalg :: GramMap -> Coalg
> coalg = Map.map $ \(t, proj) -> child_terms . proj
>   where child_terms (Match _ c t) = (c, t)

** Semantics

> type SemTree = AttrMap -> AttrMap

> type SemProd = Child :-> SemTree -> AttrMap -> SemTree

`sem_prod` is an algebra

> sem_prod :: FamRule -> SemProd
> sem_prod rule forest terminals inh = syn
>   where
>     Family syn inh_children _ = rule $ Family inh syn_children terminals
>     syn_children = forest `applyMap` inh_children

> unsafe_run :: FamRule -> InputTree -> SemTree
> unsafe_run = sem_tree . sem_prod

`sem_tree' computes the iteration of the algebra.

> sem_tree :: SemProd -> InputTree -> SemTree
> sem_tree sem_prod = sem
>   where sem (Node p cs ts) = sem_prod (Map.map sem cs) ts

A Dynamic tree coalgebra

> type Coalg =
>   NonTerminal :-> (Dynamic -> (Child :-> Dynamic, AttrMap))

Partial function, it assumes everything has been checked before.

> sem_coalg :: SemProd -> Coalg -> NonTerminal -> Dynamic -> SemTree
> sem_coalg sem_prod coalg = sem
>   where
>     sem nt dyn = sem_prod prod terms
>       where
>         (cmap, terms) = (coalg Map.! nt) dyn
>         prod = Map.mapWithKey (\k d -> sem (child_nt k) d) cmap

* Literate Haskell with org-mode
The documentation part of this literate file is written in
`org-mode'.  To benefit from the enhanced navigation given by
this mode, you should do the following to setup emacs.

- install mmm-mode

  #+BEGIN_SRC elisp
  (package install 'mmm-mode)
  #+END_SRC

- add to your .emacs:

  #+BEGIN_SRC elisp
  (mmm-add-classes
   '((literate-haskell-bird
      :submode literate-haskell-mode
      :front "^>"
      :include-front true
      :back "^[^>]*$"
      )
     ))
  #+END_SRC

Then when loading this file, use `M-x org-mode' followed by
`M-x mmm-ify-by-class' and enter `literate-haskell-bird'.

You now have both `org-mode' and `literate-haskell-mode'
together.

** Alternatively, use `occur' to generate a table of content

`M-x occur' creates an interactive buffer in which the lines
matching a regexp will link to the corresponding line in the
original buffer.

Use `occur' with regexp `^\*' to see all sections, or `^\* '
to see level-1 sections only, `^\*\* ' to see level-2
sections, `^\*\*\* ' for level-3, and so on. The syntax
`^*\{1,3\} ' can be used as well to see sections of levels 1 to 3.

** Local variables for emacs
Local Variables:
mode: org
eval: (org-indent-mode -1)
eval: (mmm-ify-by-class 'literate-haskell-bird)
eval: (local-set-key (kbd "<XF86MonBrightnessDown>") 'mmm-parse-buffer)
compile-command: "ghc AG"
End:
