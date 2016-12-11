* Overview
This file is licensed under GPL v3.

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
- Add callstack to the reader monad for aspects (cf discussion [[callstacks]])
- Make the algebra public (Production :-> SemProd) so that
  we can use the AG dsl to define algebras. (cf prettyprinting example)
  we need a typesafe version, with a way to describe the base functor!
- Template haskell to generate grammar, bindings, gramDesc
- Reorganise source code for a better presentation (easier to read an understand).
- Longer, real-world examples
- Performance comparison with UUAG
- Detecting dependencies, multi-pass execution.
** Discussion
*** <<callstacks>>
So far, when an error is detected because of a
projection, the callstack will only show the immediate
expression that called the projector, but that expression
might be far from the site where an aspect is actually
defined (with inh or syn), and may also be shared.
An example in PrettyPrinting.hs is the function
 #+BEGIN_SRC haskell
is_empty :: Child -> AR Bool
is_empty c = liftA3 zero (c!height) (c!total_width) (c!last_width)
 #+END_SRC



*** More caution with invalid Children
Defining children of a production that are not in the list of orphans.
*** Collecting errors
Note that the errors are reported per rule, not per aspect,
which means that we stop after the first rule fails.  In
order to collect errors we need to write a new `traverse'
function and use it in `runAspect'.

*** Merging aspect: duplicated rules.

Now that merging duplicated rules is an error,
we might want a way to remove some rules from an aspect
and maybe to rename attributes.

*** DONE Deletion
Deletion would involve deleting from the OutAttrs map, and
deleting from the context as well.

*** Renaming
Marcos suggested that attribute could have two fields: the
base name and a renaming function. The R monad would also
have a reader for the renaming function. Using this system we
can implement a very flexible namespace system.

* Header
** GHC Extensions

> {-# LANGUAGE
>       TypeOperators
>     , GADTs
>     , DeriveDataTypeable
>     , GeneralizedNewtypeDeriving
>  #-}

** Module Exports

- when using the library primitives, the user should never
  SEE any `Dynamic', always concrete types.
- the user should never SEE Attribute, only `Attr k a'

> module AG

*** Monoids

> ((#)

*** Maps

> , (|->), (\/)

*** General trees

> , Tree, InputTree, node

*** Context free grammar
**** Types

> , Grammar, NonTerminal, Production, Child, Children, Terminals, Name

**** Constructors

> , non_terminal, production, child, nilT, consT

**** Accessors

> , prod_nt, prod_children, child_prod, gram_children

**** DSL

> , GrammarSpec, NTSpec((::=)), ProdSpecs((:@),(:|))
> , ChildSpec((:::)), ChildrenSpec, ChildTermSpec((:&))
> , grammar, productions

*** Attributes

> , Attr, attr
> , Kind(..), I, S, T

> , Attrs, single_attr, (|=>), empty_attrs, merge_attrs, lookup_attrs -- Monoid

*** Aspects
**** Types

> , AR -- Applicative, Functor (stands for Attribution Rule)
> , Aspect -- Monoid

**** Accessors

> , context, check_aspect, missing

**** Attribute projections

> , (?),(!), chiM, chi, parM, par, terM, ter

**** Aspect constructors

> , inh, syn
> , emptyAspect, mergeAspect, concatAspects
> , delete_I, delete_S
> , inhs, syns, (|-)
> , def_S, def_I, (|=)

**** Generic rules

> , copy, copyN, copyP, copyPs, copyG
> , collect, collectAll, collectP
> , chain, chainN, chainP

*** Running the AG
**** Constraints, Contexts, Errors

We keep the context and errors abstract, we can only `show' them.

> , Context, Missing -- Show
> , Error, prettyError -- Show

**** Specification
***** Synthesized attributes

> , SynDesc, project

***** Inherited attributes

> , InhDesc, emptyInhDesc, mergeInhDesc, embed_I -- Monoid

***** Terminal attributes

> , TermDesc, termDesc

***** Tree

> , ChildDesc, childDesc, ProdDesc, prodDesc, NtDesc, ntDesc
> , GramDesc, gramDesc, insert_nt

**** Checking and Running

> , Check
> , run , runTree

*** AG Algebra
**** Specifying the input

> , AlgInput, AlgRule, projI, synAlg, emptyInput, mergeInput

*** End-of-export

> )
> where

** Module Imports

> import Prelude hiding (all, sequence, lookup)
> import Control.Applicative
> import Control.Monad.Except hiding (sequence)
> import Control.Monad.Trans.Except (except)
> import Control.Monad.Writer.Strict hiding (sequence)
> import Control.Monad.Reader hiding (sequence)
> import Data.Maybe (fromMaybe)
> import Data.List (nub, (\\), intercalate)
> import Data.Dynamic
> import Data.Function (on)
> import qualified Data.Set as Set
> import Data.Set (Set)
> import qualified Data.Map as Map
> import Data.Map (Map)
> import Data.Traversable
> import Data.Foldable (foldMap, all, traverse_)
> import GHC.Stack hiding (prettyCallStack) -- callstacks
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

> infixr 2 |->
> (|->) = Map.singleton
> infixr 1 \/
> (\/) :: Ord k => Op (k :-> a)
> (\/) = Map.union

Type of binary operators

> type Op a = a -> a -> a

 > infixr 1 #
 > (#) :: Monoid a => Op a
 > (#) = mappend

Pointwise application for finite maps.
The result is defined on the intersection of the arguments.
Since we cannot define pure, (what would the domain be?)
then it's not an applicative instance.

> applyMap :: Ord k => Map k (a -> b) -> Map k a -> Map k b
> applyMap = Map.intersectionWith ($)

A constant map over a given domain.

> constantMap :: Ord k => a -> Set k -> Map k a
> constantMap x = Set.foldr (\k -> Map.insert k x) Map.empty

Set operations

> unionSets :: Ord b => (a -> Set b) -> Set a -> Set b
> unionSets = foldMap

> symmetric op a b = (a `op` b, b `op` a)
> symdiff :: Ord a => Set a -> Set a -> (Set a, Set a)
> symdiff = symmetric Set.difference

> set_diff :: Ord a => [a] -> [a] -> Set a
> set_diff = Set.difference `on` Set.fromList

** Dynamics

> toDynP :: Typeable a => proxy a -> a -> Dynamic
> toDynP _ = toDyn

** Monads

A `traverse' that only collects errors

> collect_errors :: (MonadError e m, Foldable t) =>
>   t (m a) -> m [e]
> collect_errors = foldr cons (return [])
>  where
>    cons mx me =  (mx >> me) `catchError` handler me
>    handler me e = (e:) <$> me

> collect_error :: MonadError e m => m a -> m (Either e a)
> collect_error mx =
>   catchError (Right <$> mx) (return . Left)

> traverse_errors :: (MonadError e m, Traversable t) =>
>   (a -> m b) -> t a -> m (t (Either e b))
> traverse_errors f = traverse (collect_error . f)

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
The `AttrMap' field introduces the terminal data.

> data Tree n = Node n (Child :-> Tree n) (AttrMap T)
>             deriving Show
> type InputTree = Tree Production
> type DecoratedTree = Tree (Production, AttrMap I, AttrMap S)

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
>   , prod_terminals :: Set (Attribute T) }
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
`Attribute'.

> newtype Terminals = Terminals {terms_set :: Set (Attribute T)}

> nilT :: Terminals
> nilT = Terminals Set.empty
> consT :: Typeable a => Attr T a -> Terminals -> Terminals
> consT t (Terminals ts) =
>   Terminals $ Set.insert (Attribute t) ts

*** Misc functions

> prod_children :: Production -> Children
> prod_children p = adopt <$> prod_orphans p
>   where adopt (c,n) = Child (p,c) n

> prod_nt :: Production -> NonTerminal
> prod_nt = fst . prod_name

> child_prod :: Child -> Production
> child_prod = fst . child_name

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
orphans have unique names for each production.

> valid_grammar :: Grammar -> Bool
> valid_grammar = all valid_production

Children of a production must have unique names.
Note: if two terminals have the same name but different types
then they are different: only their names are overloaded.

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

*** Attr, Attribute

> data Attr k a = Attr
>   { attr_name :: Name
>   , attr_kind :: Kind k}

> attr :: Typeable a => Name -> Kind m -> p a -> Attr m a
> attr n k _ = Attr n k

> data Attribute k where
>   Attribute :: Typeable a => Attr k a -> Attribute k

**** Eq, Ord, Show
WARNING: what if two attributes with the same name and
different types are used? If we consider them equal then the
value associated to the name could change type.  If we
consider them different then it should behave just fine.  The
names are overloaded but we can distinguish the concrete
attributes by their types.

> lexicographic EQ c = c
> lexicographic c _ = c

> eqAttr :: (Typeable a, Typeable a') =>
>   Attr k a -> Attr k' a' -> Bool
> eqAttr x y =
>   x `compareAttr` y  == EQ

> compareAttr :: (Typeable a, Typeable a') =>
>   Attr k a -> Attr k' a' -> Ordering
> compareAttr a@(Attr x j) b@(Attr y k) =
>     (x `compare` y)
>     `lexicographic` ((j `compareKind` k)
>                      `lexicographic` (typeRep a `compare` typeRep b))

> instance Eq (Attribute k) where
>   Attribute x == Attribute y  =  x `eqAttr` y

> instance Ord (Attribute k) where
>   Attribute x `compare` Attribute y  =  x `compareAttr` y

> instance Show (Attr k a) where
>   show = attr_name

> instance Show (Attribute k) where
>   show (Attribute x) = show x

*** Attributions
An attribution is a finite map from attribute name to values.
Note: the use of Dynamics prevents us from having polymorphic
attributes.

> type AttrSet k = Set (Attribute k)
> type AttrMap k = Attribute k :-> Dynamic
> emptyAttrs :: AttrMap k
> emptyAttrs = Map.empty
> mergeAttrs :: Op (AttrMap k)
> mergeAttrs = Map.union

Note: we do an unsafe conversion, because lookupAttr will
only be called after the AG has been typechecked at runtime.

> lookupAttr :: (Typeable a) => Attr k a -> AttrMap k -> Maybe a
> lookupAttr a m =
>   (\d -> fromDyn d (err d))
>   <$> Map.lookup (Attribute a) m
>   where
>     err d = error $ "[BUG] lookupAttr:" ++ attr_type_err a d

> attr_type_err a d = "attribute " ++ show a
>             ++ ", expected type: " ++ show (typeRep a)
>             ++ ", runtime type: " ++ show (dynTypeRep d)

> projAttr :: Typeable a => AttrMap k -> Attr k a -> Maybe a
> projAttr = flip lookupAttr
> singleAttr :: Typeable a => Attr k a -> a -> AttrMap k
> singleAttr a x = Attribute a |-> toDyn x

> delete_attr :: Typeable a => Attr k a -> AttrMap k -> AttrMap k
> delete_attr = Map.delete . Attribute

**** Parent, children and terminal attributions.

> type ChildrenAttrs k = Child :-> AttrMap k
> emptyChildrenAttrs :: ChildrenAttrs k
> emptyChildrenAttrs = Map.empty
> mergeChildrenAttrs :: Op (ChildrenAttrs k)
> mergeChildrenAttrs x y =
>   Map.unionWith mergeAttrs x y

**** Input and output attributes

A rule is a function that computes the attributes of a
production, it is a map from input attributes to output
attributes.

The input attributes consists of the inherited attributes for
the parent of the production, the synthesized
attributes of the children and the terminal attributes.

> type InAttrs = (AttrMap I, ChildrenAttrs S, AttrMap T)

The output attributes consists of the synthesized attributes
for the parent of the production and the inherited attributes
of the children.

> type OutAttrs = (AttrMap S, ChildrenAttrs I)

> parentAttrs :: InAttrs -> AttrMap I
> childrenAttrs :: InAttrs -> ChildrenAttrs S
> terminalAttrs :: InAttrs -> AttrMap T

> parentAttrs (p,c,t) = p
> childrenAttrs (p,c,t) = c
> terminalAttrs (p,c,t) = t

> emptyOutAttrs :: OutAttrs
> emptyOutAttrs =
>   (emptyAttrs, emptyChildrenAttrs)

Note: merging the output attributes is not symmetrical: the
left attribution has priority over the right attribution in
case of a conflict, i.e. when the same attribute is given a
value by both attributions, the left definition will be
chosen over the right one. However, the primitive to merge
rules will throw an error if any conflict occurs.

> mergeOutAttrs :: Op OutAttrs
> mergeOutAttrs (x, xs) (y, ys) =
>   ( mergeAttrs x y
>   , mergeChildrenAttrs xs ys)

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
> constr_attr :: Constraint k t -> Attribute k
> constr_attr (Constraint a x) = Attribute a

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

> type Lens a b = (a -> (b, b -> a))
> lens_ensure_I ctx = (ensure_I ctx, \x -> ctx {ensure_I = x})
> lens_ensure_S ctx = (ensure_S ctx, \x -> ctx {ensure_S = x})

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
>     ensure (Attribute a) = Constraint a p

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

> newtype Missing = Missing (Set Ensure_I, Set Ensure_S, Set Ensure_T) deriving Show
> nullMissing (Missing (x,y,z)) = Set.null x && Set.null y && Set.null z

> missing ::
>   Grammar -> Context -> Missing
> missing g c = Missing
>   ( unionSets (missing_I (gram_children g) (ensure_I c)) (require_I c)
>   , unionSets (missing_S g (ensure_S c)) (require_S c)
>   , missing_T (ensure_T g) (require_T c))

> missing_K :: (Ord a) =>
>   (a -> NonTerminal) -> Set a -> Set (Constraint k a) -> Constraint k NonTerminal -> Set (Constraint k a)
> missing_K proj_nt object ensure r@(Constraint a n) =
>   Set.difference match_object match_ensure
>  where
>     match_object =
>       Set.map (<$ r)
>        $ Set.filter ((== n) . proj_nt) object
>     match_ensure =
>       Set.filter ((== r) . fmap proj_nt) ensure

> missing_I = missing_K child_nt
> missing_S = missing_K prod_nt

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

> assert_child :: HasCallStack => Child -> A ()
> assert_child c = do
>   p <- current_production
>   unless (c `elem` prod_children p)
>     $ throwErrorA (Error_Rule_Invalid_Child c p)

> cstr :: Typeable a =>
>   Attr k a -> t -> Set (Constraint k t)
> cstr a x =
>   Set.singleton (Constraint a x)

> require_child :: (HasCallStack, Typeable a) =>
>   Child -> Attr S a -> A ()
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

* Rules and Aspects
** A and R monads
An attribute grammar is given by a context free grammars and
attribution rules.

 > type AG = (Grammar, Rule)

In order to check that the rules are compatible with a
grammar, we must collect information about the rules:

Which attributes are used and with which type from the
parent, the children, or the terminal data..

To capture this information we will use monads.

In order to gather information from the use of input attributes, we
must define rule in a specific monad in which the input attributes
is accessed through primitives.

> newtype R a = R {runR :: Reader InAttrs a} -- the rule monad
>   deriving (Functor, Applicative, Monad, MonadReader InAttrs)

In order to compute rules, we must first check that they are
valid.  Rules are defined in the context of a production, and
may fail if some constraints are not met, like using a child
that is not a valid child of the current production.
And lastly, we collect constraints.

> newtype A a = A (ReaderT Production (ExceptT Error (Writer Context)) a) -- the aspect monad
>   deriving (Functor, Applicative, Monad, MonadReader Production, MonadError Error, MonadWriter Context)

private

> runA :: A a -> Production -> (Check a, Context)
> runA (A a) p =
>   runWriter . runExceptT $ runReaderT a p

> current_production :: A Production
> current_production = ask

** AR applicative

AR stands for Attribution Rule

> newtype AR a = AR {runAR :: A (R a)}

> instance Applicative AR where
>   pure x = AR (pure (pure x))
>   AR f <*> AR x = AR ((<*>) <$> f <*> x)
> instance Functor AR where
>   fmap f x = pure f <*> x

*** Private

> inAR f (AR x) = AR (f x)

** Rule
A rule takes an inherited attribution for the parents, and
synthesized attributions for the children and compute a
synthesized attribution for the parents and inherited
attributions for the children.

Rule is private.

> type PureRule = InAttrs -> OutAttrs
> type Rule = AR OutAttrs

> rule_context :: Rule -> Context
> rule_context (AR r) = snd $ runA r err
>   where err = error "[BUG] rule_context: unexpected use of production."

> emptyRule :: Rule
> emptyRule = pure emptyOutAttrs

Merging rules whose domain overlap is an error.

> mergeRule :: HasCallStack => Op Rule
> mergeRule left_rule right_rule
>   | not (Set.null duplicate_inh) =
>       AR $ throwErrorA $ Error_Rule_Merge_Duplicate_I duplicate_inh
>   | not (Set.null duplicate_syn) =
>       AR $ throwErrorA $ Error_Rule_Merge_Duplicate_S duplicate_syn
>   | otherwise = liftA2 mergeOutAttrs left_rule right_rule
>   where
>     left_ctx = rule_context left_rule
>     right_ctx = rule_context right_rule
>     dup proj = (Set.intersection `on` proj) left_ctx right_ctx
>     duplicate_inh = dup ensure_I
>     duplicate_syn = dup ensure_S

`delete_rule_I a c rule' removes the definition of the attribute
`a' associated with child `c' from `rule'. It is an error
if this definition is not provided by `rule'.

> delete_rule_I :: Typeable a =>
>   Attr I a -> Child -> Rule -> Rule
> delete_rule_I a c =
>   delete_rule Error_Rule_Delete_Missing_I lens_ensure_I
>               delete_outattrs_I (Constraint a c)

`delete_rule_S a p rule' removes the definition of the attribute
`a' associated with production `p' from `rule'. It is an error
if this definition is not provided by `rule'.

> delete_rule_S :: Typeable a =>
>   Attr S a -> Production -> Rule -> Rule
> delete_rule_S a p =
>   delete_rule Error_Rule_Delete_Missing_S lens_ensure_S
>               delete_outattrs_S (Constraint a p)

> delete_outattrs_I :: Ensure_I -> OutAttrs -> OutAttrs
> delete_outattrs_I (Constraint a c) (ps, ci) =
>   (ps, Map.adjust (delete_attr a) c ci)

> delete_outattrs_S :: Ensure_S -> OutAttrs -> OutAttrs
> delete_outattrs_S (Constraint a p) (ps, ci) =
>   (delete_attr a ps, ci)

> delete_rule :: (Ord t) =>
>   (Constraint k t -> ErrorMsg) ->
>   Lens Context (Set (Constraint k t)) ->
>   (Constraint k t -> OutAttrs -> OutAttrs) ->
>   Constraint k t -> Rule -> Rule
> delete_rule err lens del cstr =
>   inAR $ censor del_constraint . del_attr
>  where
>   del_constraint ctx =
>     let (ensure, modify) = lens ctx
>     in modify $ Set.delete cstr ensure
>   del_attr r = do
>     (rout, ctx) <- listen $ fmap (fmap (del cstr)) r
>     when (not . Set.member cstr . fst $ lens ctx) $
>       throwErrorA $ err cstr
>     return rout

** Aspect

> type PureAspect = Production :-> PureRule
> newtype Aspect = Aspect (Production :-> Rule)
> inAspect f (Aspect x) = Aspect (f x)
> inAspect2 f (Aspect x) (Aspect y) = Aspect (f x y)
> emptyAspect = Aspect $ Map.empty

> mergeAspect, (#) :: HasCallStack => Aspect -> Aspect -> Aspect
> mergeAspect = withFrozenCallStack $ inAspect2 $ Map.unionWith mergeRule
> (#) = withFrozenCallStack mergeAspect

> instance Monoid Aspect where
>   mempty = emptyAspect
>   mappend = mergeAspect

> concatAspects :: [Aspect] -> Aspect
> concatAspects = mconcat

`delete_I a c aspect' removes the definition of the attribute
`a' associated with child `c' from `aspect'. It is an error
if this definition is not provided by `aspect'.

> delete_I :: Typeable a =>
>   Attr I a -> Child -> Aspect -> Aspect
> delete_I a c = inAspect $
>   Map.adjust (delete_rule_I a c) (child_prod c)

`delete_S a p aspect' removes the definition of the attribute
`a' associated with production `p' from `aspect'. It is an error
if this definition is not provided by `aspect'.

> delete_S :: Typeable a =>
>   Attr S a -> Production -> Aspect -> Aspect
> delete_S a p = inAspect $
>   Map.adjust (delete_rule_S a p) p

`runAspect` is private. Note: the production in the readerT
is not used for rules.  Because when we build rules we always
override the production with a call to `local' (see the code
of `inh' and `syn').
Note: we collect the errors from each production.

> runAspect :: Aspect -> (Check PureAspect, Context)
> runAspect (Aspect asp) = (asp_err, ctx)
>  where
>    errors_ag = fst $ runA (collect_errors $ runAR <$> asp) err
>    (asp_ag, ctx) = runA asp_a err
>    asp_err = do
>      errors <- errors_ag
>      if null errors then asp_ag
>      else throwErrorCheck $ Errors errors
>    asp_ar = traverse runAR asp -- A (Production :-> R OutAttrs)
>    asp_a  = liftM (Map.map (runReader  . runR)) asp_ar -- A PureAspect
>    err = error "[BUG] runAspect: unexpected use of production."

> context :: Aspect -> Context
> context = snd . runAspect

> check_aspect :: Aspect -> IO ()
> check_aspect a = case fst (runAspect a) of
>   Left e -> putStr $ prettyError e
>   Right _ -> putStrLn "OK"

* Error datatype

> data ErrorMsg
>   = Error_Rule_Invalid_Child Child Production
>   | Error_Rule_Merge_Duplicate_I (Set Ensure_I)
>   | Error_Rule_Merge_Duplicate_S (Set Ensure_S)
>   | Error_Rule_Delete_Missing_I Ensure_I
>   | Error_Rule_Delete_Missing_S Ensure_S
>   | Error_InhDesc_Duplicate [Attribute I] -- raised when checking InhDesc
>   | Error_InhDesc_Missing (Set Require_I) -- raised when checking InhDesc and rules
>   | Error_SynDesc_Missing (Set Ensure_S) -- raised when checking SynDesc, Grammar and rules
>   | Error_ProdDesc_Duplicate_Children [Child] Production
>   | Error_ProdDesc_Invalid_Children (Set Child) Production
>   | Error_ProdDesc_Missing_Children (Set Child) Production
>   | Error_ProdDesc_Duplicate_Terminals [Attribute T] Production
>   | Error_ProdDesc_Invalid_Terminals (AttrSet T) Production
>   | Error_ProdDesc_Missing_Terminals (AttrSet T) Production
>   | Error_NtDesc_Duplicate_Productions [Production] NonTerminal
>   | Error_NtDesc_Invalid_Productions (Set Production) NonTerminal
>   | Error_GramDesc_Duplicate NonTerminal
>   | Error_GramDesc_Missing (Set NonTerminal)
>   | Error_GramDesc_Wrong_Types (Set Child)
>   | Error_Production_Duplicate_Children_Names [Name] Production
>   | Error_Missing Missing
>   | Error_Tree_Invalid_Children (Set Child) Production
>   | Error_Tree_Missing_Children (Set Child) Production
>   | Error_Tree_Invalid_Terminals (AttrSet T) Production
>   | Error_Tree_Missing_Terminals (AttrSet T) Production
>   | Error_RunTree_Missing (Set Require_I)
>   | Error_Algebra_Different_Productions Production Production
>   | Error_Algebra_Invalid_Children (Set Child) Production
>   | Error_Algebra_Missing_Children (Set Child) Production
>   | Errors [Error]
>   deriving Show

** Callstack

> newtype Error = Error (ErrorMsg, CallStack) deriving Show

> throwErrorA :: HasCallStack => ErrorMsg -> A a
> throwErrorA e = throwError (Error (e, popCallStack callStack))

> throwErrorCheck :: HasCallStack => ErrorMsg -> Check a
> throwErrorCheck e = throwError (Error (e, popCallStack callStack))

** pretty printing

> prettyError :: Error -> String
> prettyError (Error (e,c)) =
>   "AG:Error: " ++ prettyErrorMsg e ++ prettyCallStack c ++ "\n"

> prettyErrorMsg (Errors es) = --unlines $ map prettyError es
>   unlines $ show_errs <$> Map.toList (group_errors es)
>   where show_errs (c,es) = c ++ "\n" ++ unlines (prettyErrorMsg <$> es)

> prettyErrorMsg e = case e of
>   Error_Rule_Invalid_Child c p ->
>     "child " ++ show c ++ " does not belong to production " ++ show p
>   Error_Rule_Merge_Duplicate_I es ->
>     "merging conflict: "
>     ++ show_set es
>   Error_Rule_Merge_Duplicate_S es ->
>     "merging conflict: "
>     ++ show_set es
>   Error_Rule_Delete_Missing_I c ->
>     "missing attribution while trying to delete:" ++ show c
>   Error_Rule_Delete_Missing_S c ->
>     "missing attribution while trying to delete:" ++ show c
>   Error_InhDesc_Duplicate cs ->
>     "InhDesc, some inherited attributes for the root were specified more that once: "
>     ++ show_list cs
>   Error_InhDesc_Missing cs ->
>     "InhDesc: some inherited attributes were not specified for the root: "
>     ++ show_set cs
>   Error_SynDesc_Missing cs ->
>     "SynDesc: some attributes do not have a corresponding definition: " ++ show_set cs
>   Error_ProdDesc_Duplicate_Children cs p -> --[Child] Production
>     "ProdDesc: some children have been specified more that once for production " ++ show p ++ ": " ++ show_list cs
>   Error_ProdDesc_Invalid_Children cs p -> --(Set Child) Production
>     "ProdDesc: some children are not valid in production " ++ show p ++ ": " ++ show_set cs
>   Error_ProdDesc_Missing_Children cs p -> --(Set Child) Production
>     "ProdDesc: some children were not specified for production " ++ show p ++ ": " ++ show_set cs
>   Error_ProdDesc_Duplicate_Terminals ts p ->
>     "ProdDesc: some terminals were specified more than once for production " ++ show p ++ ": " ++ show_list ts
>   Error_ProdDesc_Invalid_Terminals ts p -> -- (AttrSet T) Production
>     "ProdDesc: some terminals do not belong in production " ++ show p ++ ": " ++ show_set ts
>   Error_ProdDesc_Missing_Terminals ts p -> --(AttrSet T) Production
>     "ProdDesc: some terminals were not specified for production " ++ show p ++ ": " ++ show_set ts
>   Error_NtDesc_Duplicate_Productions ps n -> -- [Production] NonTerminal
>     "NtDesc: some productions were specified more than once for non-terminal " ++ show n ++ ": " ++ show_list ps
>   Error_NtDesc_Invalid_Productions ps n -> --(Set Production) NonTerminal
>     "NtDesc: some productions do not belong in non-terminal " ++ show n ++ ": " ++ show_set ps
>   Error_GramDesc_Duplicate n -> --NonTerminal
>     "GramDesc: non-terminal " ++ show n ++ " was specified more than once."
>   Error_GramDesc_Missing ns -> --(Set NonTerminal)
>     "GramDesc: some non-terminal were not specified " ++ show ns
>   Error_GramDesc_Wrong_Types cs -> --(Set Child)
>     "GramDesc: the concrete type of some child(ren) does not correspond to the concrete type of their non-terminal: "
>     ++ show_set cs
>   Error_Production_Duplicate_Children_Names ns p -> --[Name] Production
>     "ill-formed production: " ++ show p ++ ", the list of children contains more that once the same names: "
>     ++ show_list ns
>   Error_Missing ms -> -- Missing
>     "incomplete attribute definitions, missing: " ++ show ms
>   Error_Tree_Invalid_Children cs p -> --(Set Child) Production
>     "runTree: some children are not valid in production: " ++ show p
>     ++ ": " ++ show_set cs
>   Error_Tree_Missing_Children cs p -> --(Set Child) Production
>     "runTree: some children are missing in production: " ++ show p
>     ++ ": " ++ show_set cs
>   Error_Tree_Invalid_Terminals ts p -> -- (AttrSet T) Production
>     "runTree: some terminals are not valid in production: " ++ show p
>     ++ ": " ++ show_set ts
>   Error_Tree_Missing_Terminals ts p -> --(AttrSet T) Production
>     "runTree: some terminals are missing in production: " ++ show p
>     ++ ": " ++ show_set ts
>   Error_RunTree_Missing cs -> --(Set Require_I)
>     "runTree: some inherited attributes were not specified for the root: "
>     ++ show_set cs
>   _ -> show e

*** Auxiliary definitions

> show_list :: Show a => [a] -> String
> show_list s = intercalate ", " (show <$> s)

> show_set :: Show a => Set a -> String
> show_set = show_list . Set.toList


> prettyCallStack :: CallStack -> String
> prettyCallStack = intercalate "\n" . prettyCallStackLines

> prettyCallStackLines :: CallStack -> [String]
> prettyCallStackLines cs = case getCallStack cs of
>   []  -> []
>   stk -> map (("  " ++) . prettyCallSite) stk
>   where
>     prettyCallSite (f, loc) = f ++ " at " ++ prettySrcLoc loc

Builds a map from callstacks to error messages Note: i build
the map using the string representation, that's not ideal:
I should define an Ord instance for CallStacks.

> group_errors = foldr cons Map.empty
>  where cons (Error (e, c)) = Map.insertWith mappend (prettyCallStack c) [e]

* Rules and Aspect primitives
** Attribute projections
Rules are defined in an applicative `AR', that comes with
primitives to project attributes from either the parent, a
child of the production or the terminal child.  Those
primitive generate `Require' constraints.

The `Maybe' versions of `chi', `par' and `ter' do not add any
constraints: their success or failure is captured by the
Maybe monad at runtime.

Children attribute

> (?), chiM ::  (HasCallStack, Typeable a) =>
>   Child -> Attr S a -> AR (Maybe a)
> (?) c a = withFrozenCallStack $ AR $ return $ do
>   cs <- asks childrenAttrs
>   return $ lookupAttr a =<< Map.lookup c cs

> chiM = (?)

Parent attribute

> parM :: (HasCallStack, Typeable a) =>
>   Attr I a -> AR (Maybe a)
> parM a = withFrozenCallStack $ AR $ return $ do
>  lookupAttr a <$> asks parentAttrs
>

Terminal attribute

> terM :: (HasCallStack, Typeable a) =>
>   Attr T a -> AR (Maybe a)
> terM a = withFrozenCallStack $ AR $ return $ do
>   lookupAttr a <$> asks terminalAttrs

The strict versions are all instances of the following
function, which adds a constraint before safely forcing the
evaluation of the attribute.

> strictProj :: (HasCallStack, Typeable a) =>
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
> (!), chi :: (HasCallStack, Typeable a) =>
>   Child -> Attr S a -> AR a
> (!) c = withFrozenCallStack $
>   strictProj (c ?) (require_child c)
> chi = (!)

> par :: (HasCallStack, Typeable a) =>
>   Attr I a -> AR a
> par = withFrozenCallStack .
>   strictProj parM require_parent

> ter :: (HasCallStack, Typeable a) =>
>   Attr T a -> AR a
> ter = withFrozenCallStack .
>   strictProj terM require_terminal

(private) Common boiler plate to build a rule (shared by inh and syn)

> build_aspect :: Typeable a =>
>   Attr k a ->
>   Production ->
>   A () ->
>   (AttrMap k -> OutAttrs) ->
>   AR a -> Aspect
> build_aspect attr production constraint fam rule =
>   Aspect $ Map.singleton production $ AR $ do
>     rule' <- local (const production) (constraint >> runAR rule)
>     return $ fam' <$> rule'
>   where
>     fam' x = fam $ singleAttr attr x

** Aspect constructors

Inherited attributes are defined for a specific child of a
production.  The production is determined by the Child.

> inh :: (HasCallStack, Typeable a) =>
>   Attr I a -> Child -> AR a -> Aspect
> inh a c = build_aspect a (child_prod c) (ensure_child c a)
>   $ \attrs -> (emptyAttrs, c |-> attrs)

Synthesized attributes are defined for the parent of a production.

> syn :: (HasCallStack, Typeable a) =>
>   Attr S a -> Production -> AR a -> Aspect
> syn a p = build_aspect a p (ensure_parent a)
>   $ \attrs -> (attrs, emptyChildrenAttrs)

** Derived combinators
*** One attribute, multiple definitions
Nicer pairs for association lists [(a,b)]

> infixr 2 |-
> x |- y = (x,y)

> inhs :: Typeable a => Attr I a -> [(Child, AR a)] -> Aspect
> inhs a = foldl (\rs (c,r) -> rs # inh a c r) emptyAspect

> syns :: Typeable a => Attr S a -> [(Production, AR a)] -> Aspect
> syns a = foldl (\rs (p,r) -> rs # syn a p r) emptyAspect

*** One production, multiple attributes

> infixr 2 |=
> x |= y = AttrDef x y

> data AttrDef k where
>   AttrDef :: Typeable a => Attr k a -> AR a -> AttrDef k

> def_S :: Production -> [AttrDef S] -> Aspect
> def_S p = foldl (\rs (AttrDef a r) -> rs # syn a p r) emptyAspect

> def_I :: Child -> [AttrDef I] -> Aspect
> def_I c = foldl (\rs (AttrDef a r) -> rs # inh a c r) emptyAspect

* Generic rules

Note that all those rules are in only using the public
primitives and could be defined by the user.

** Copy
`copy' copies the attribute the parent to the child.

> copy :: Typeable a => Attr I a -> Child -> Aspect
> copy a c = inh a c (par a)

`copyN' takes a list of children for which the attribute is
to be copied.

> copyN :: Typeable a => Attr I a -> Children -> Aspect
> copyN a cs = concatAspects . map (copy a) $ cs

`copyP' copies the inherited attribute of the parent to all
the children that have the same non-terminal.

> copyP :: Typeable a => Attr I a -> Production -> Aspect
> copyP a p = copyN a cs
>   where cs = [ c | c <- prod_children p
>                  , child_nt c == prod_nt p ]

`copyPs' implements the copy rule for a list of production.

> copyPs :: Typeable a => Attr I a -> [Production] -> Aspect
> copyPs a = foldr (\p r -> copyP a p # r) emptyAspect

`copyG' implements the copy rule for all the productions of a
non-terminal in a given grammar.

> copyG :: Typeable a => Attr I a -> NonTerminal -> Grammar -> Aspect
> copyG a n g = copyPs a [p | p <- Set.toList g, prod_nt p == n]

** Collect
`collect' applies a function to the attributes of a list of children
to compute a synthesized attribute.

> collect :: Typeable a => Attr S a -> ([a] -> a) -> Production -> Children -> Aspect
> collect a reduce p cs = syn a p $
>   reduce <$> traverse (!a) cs

`collectAll' applies the function to all the attributes for
all children that implement it. It doesn't add any require
constraints.

> collectAll :: Typeable a => Attr S a -> ([a] -> a) -> Production -> Aspect
> collectAll a reduce p = syn a p $
>   (reduce . filterJust) <$> traverse (?a) (prod_children p)

`collectP' applies the function to the attributes of all the
children that have the same non-terminal as the parent.
By hypothesis, we know that the attribute will be defined for them.

> collectP :: Typeable a => Attr S a -> ([a] -> a) -> Production -> Aspect
> collectP a reduce p = syn a p $ reduce <$> traverse (!a) cs
>  where cs = [ c | c <- prod_children p, child_nt c == prod_nt p ]

** Chain

The chain rule takes a pair of an inherited and a synthesized
attribute and thread them through the children of a
production: the parent attribute is given to the first child,
the attribute of the first child is given to the second and
so on, the attribute of the last child is given back to the
parent. So, this rule defines the inherited attribute for all
the children and the synthesized attribute for the parent.

> chain :: Typeable a =>
>   Attr I a -> Attr S a -> Production -> Children -> Aspect
> chain i s p cs =
>   (inhs i $ zip cs $ par i : ((!s) <$> init cs))
>   # syn s p (last cs ! s)

Applies the chain rule the children of a production having
the given (non-terminal).

> chainN :: Typeable a =>
>   Attr I a -> Attr S a -> Production -> [NonTerminal] -> Aspect
> chainN i s p ns = chain i s p cs
>   where cs = [ c | c <- prod_children p, child_nt c `elem` ns]

Applies the chain rule the children of a production having
the same non-terminal as the parent.

> chainP :: Typeable a =>
>   Attr I a -> Attr S a -> Production -> Aspect
> chainP i s p = chainN i s p [prod_nt p]

* Running the grammar

** Running on a concrete type
*** Specifying input and output
Rather than run the AG on the general tree type.
We must build (total) conversions between
- t and the tree type,
- i,s and the AttrMap type.

To specify i and s, we must keep track of the attributes that
they will be using and build conversion functions
(i -> AttrMap) and (AttrMap -> s).

**** Synthesized attributes
For the synthesized attributes the following interface is enough.

SynDesc is abstract

> newtype SynDesc s = SynDesc { runSynDesc ::
>   Writer (Set (Attribute S)) (AttrMap S -> s) }

> instance Functor SynDesc where
>   fmap f x = pure f <*> x

> instance Applicative SynDesc where
>   pure x = SynDesc $ return $ pure x
>   SynDesc f <*> SynDesc x =
>     SynDesc $ liftM2 (<*>) f x

> project :: Typeable a => Attr S a -> SynDesc a
> project a = SynDesc $ do
>   tell (Set.singleton (Attribute a))
>   return $ fromMaybe err . lookupAttr a
>  where
>    err = error $ "[BUG] project: undefined attribute " ++ show a

***** Private

> proj_S :: SynDesc s -> AttrMap S -> s
> proj_S = fst . runWriter . runSynDesc

**** Inherited attributes

> newtype InhDesc t  = InhDesc { runInhDesc ::
>    Writer ([Attribute I]) (t -> AttrMap I) }

> emptyInhDesc :: InhDesc t
> emptyInhDesc = InhDesc $ return $ pure $ Map.empty

> embed_I :: Typeable a =>
>   Attr I a -> (i -> a) -> InhDesc i
> embed_I a p = InhDesc $ do
>   tell [Attribute a]
>   return $ Map.singleton (Attribute a) . toDyn . p

> mergeInhDesc :: InhDesc t -> InhDesc t -> InhDesc t
> InhDesc x `mergeInhDesc` InhDesc y =
>   InhDesc $ liftA2 union x y
>  where
>    union f g = \x -> Map.union (f x) (g x)

> instance Monoid (InhDesc t) where
>   mempty = emptyInhDesc
>   mappend = mergeInhDesc

***** Private

> proj_I :: InhDesc i -> i -> AttrMap I
> proj_I = fst . runWriter . runInhDesc

**** Example

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

*** Concrete tree specification

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

**** ChildDesc
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

**** TermDesc

> data TermDesc t = TermDesc
>   { termDesc_attr :: Attribute T
>   , termDesc_proj :: t -> Maybe (Attribute T, Dynamic) }

> termDesc :: (Typeable a, Typeable b) =>
>   Attr T b -> (a -> Maybe b) -> TermDesc a
> termDesc a p = TermDesc a' p'
>   where
>     a' = Attribute a
>     p' x = (\y -> (a', toDyn y)) <$> p x

**** ProdDesc

`ProdDesc a' describes a constructor of the type `a' (viewed
as a grammar production).

> newtype ProdDesc t = ProdDesc { runProdDesc ::
>   Check (ProdDescRec t) }

> data ProdDescRec t = ProdDescRec
>   { prodDesc_prod :: Production
>   , prodDesc_children_types :: Child :-> TypeRep
>   , prodDesc_match :: t -> Maybe (Child :-> Dynamic, AttrMap T) }

`prodDesc' associates a production to a constructor.

- the children must be children of the production.
- all the production's children are provided
- all the production's terminals are provided

Note: No error is raised if the termDesc produces more
terminals than the production needs.  we will just ignore
them.

> prodDesc :: (Typeable a) =>
>   Production -> [ChildDesc a] -> [TermDesc a] -> ProdDesc a
> prodDesc prod cds tds = ProdDesc $ this
>  where
>  this
>   | not (null duplicate_children) =
>       throwErrorCheck $ Error_ProdDesc_Duplicate_Children duplicate_children prod
>   | not (Set.null invalid_children) =
>       throwErrorCheck $ Error_ProdDesc_Invalid_Children invalid_children prod
>   | not (Set.null missing_children) =
>       throwErrorCheck $ Error_ProdDesc_Missing_Children missing_children prod
>   | not (null duplicate_terminals) =
>       throwErrorCheck $ Error_ProdDesc_Duplicate_Terminals duplicate_terminals prod
>   | not (Set.null invalid_terminals) =
>       throwErrorCheck $ Error_ProdDesc_Invalid_Terminals invalid_terminals prod
>   | not (Set.null missing_terminals) =
>       throwErrorCheck $ Error_ProdDesc_Missing_Terminals missing_terminals prod
>   | otherwise = return $ ProdDescRec prod children_types match
>   where
>     match = liftA2 (liftA2 (,)) child_proj term_proj
>     children_types = Map.fromList $ child_type <$> cds
>     child_type c = (childDesc_child c, childDesc_type c)
>     child_proj = fmap Map.fromList . sequence . traverse childDesc_proj cds
>     ts = termDesc_attr <$> tds
>     term_attrs = Set.fromList ts
>     term_proj = fmap Map.fromList . sequence . traverse termDesc_proj tds
>     -- Checking children
>     duplicate_children = duplicates cs
>     ( invalid_children
>      , missing_children) = symmetric set_diff cs (prod_children prod)
>     cs = childDesc_child <$> cds
>     -- Checking terminals
>     duplicate_terminals = duplicates ts
>     prod_terms = prod_terminals prod
>     ( invalid_terminals
>      , missing_terminals) = symdiff term_attrs prod_terms

**** NtDesc

`NtDesc a' associates a non-terminal to the datatype `a'

> newtype NtDesc t = NtDesc { runNtDesc ::
>   Check (NtDescRec t) }

> data NtDescRec t = NtDescRec
>   { ntDesc_nt :: NonTerminal
>   , ntDesc_prods :: Set Production
>   , ntDesc_children_types :: Child :-> TypeRep
>   , ntDesc_match :: t -> Match }

> data Match =
>   Match { math_prod :: Production -- we don't actually need it to run the AG.
>         , match_child :: Child :-> Dynamic
>         , match_terminals :: AttrMap T }

- all productions must belong to the given non-terminal
- productions must be distincts

> ntDesc :: (Typeable a) =>
>   NonTerminal -> [ProdDesc a] -> NtDesc a
> ntDesc nonterm agps =
>   NtDesc $ this =<< sequence (runProdDesc <$> agps)
>  where
>   this :: [ProdDescRec a] -> Check (NtDescRec a)
>   this ps
>    | not (null duplicate_prods) =
>        throwErrorCheck $ Error_NtDesc_Duplicate_Productions duplicate_prods nonterm
>    | not (Set.null invalid_prods) =
>        throwErrorCheck $ Error_NtDesc_Invalid_Productions invalid_prods nonterm
>    | otherwise = return $ NtDescRec nonterm productions children_types (match ps)
>    where
>      productions = Set.fromList prodlist
>      children_types = Map.unions (prodDesc_children_types <$> ps)
>      -- Pattern matching function
>      match [] x = error "ntDesc: match failure due to incorrect gramDesc specification." -- or bug
>      match (p:ps) x =
>        maybe (match ps x)
>              (\(cs, ts) -> Match (prodDesc_prod p) cs ts)
>          $ prodDesc_match p x
>      -- Checking the production
>      prodlist = prodDesc_prod <$> ps
>      duplicate_prods = duplicates prodlist
>      invalid_prods = Set.filter ((nonterm /=) . prod_nt) productions

**** GramDesc

`GramDesc a' associates a grammar to a family of types, where
`a' is associated to the start symbol of the grammar: the
root of the tree will have type `a'.

- The child_type map is used later to check that the
  non-terminal associated with each child corresponds with
  the typeRep associated with each `childDesc'.

> newtype GramDesc a = GramDesc { runGramDesc ::
>   Check (NonTerminal, Grammar, Child :-> TypeRep, GramMap) }

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
>     $ throwErrorCheck $ Error_GramDesc_Duplicate nt
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

*** Checking the AG

The Check monad

> type Check a = Either Error a

Unique attributes

> check_inh_unique ::
>   InhDesc i -> Check ()
> check_inh_unique desc
>   | null xs' = return ()
>   | otherwise = throwErrorCheck $ Error_InhDesc_Duplicate xs'
>   where
>     (proj, xs) = runWriter . runInhDesc $ desc
>     xs' = duplicates xs

All the required inherited attributes have been specified for
the root.

> check_inh_required ::
>   InhDesc i -> NonTerminal -> Set Require_I -> Check ()
> check_inh_required =
>   check_attrs Error_InhDesc_Missing . inhAttrs
>   where
>     inhAttrs = Set.fromList . snd . runWriter . runInhDesc


All the synthesized attributes accessed from the root are
ensured by the rules.

> check_syn_ensured ::
>   SynDesc s -> Grammar -> NonTerminal -> Set Ensure_S -> Check ()
> check_syn_ensured desc prods root ens
>   | Set.null missing = return ()
>   | otherwise = throwErrorCheck $ Error_SynDesc_Missing missing
>   where
>     missing = unionSets (missing_S prods ens) ss'
>     ss' = Set.map cstr ss
>     cstr (Attribute a) = Constraint a root
>     (proj, ss) = runWriter . runSynDesc $ desc

The non-terminal associated with each child must correspond
with the typeRep associated with each `childDesc'.

> check_gramDesc ::
>   GramDesc a -> Check (NonTerminal, Grammar, GramMap)
> check_gramDesc (GramDesc g) = do
>   (nt, gram, ctypes, grammap) <- g
>   check_children_types ctypes grammap
>   return $ (nt, gram, grammap)

> check_children_types ::
>   Child :-> TypeRep -> GramMap -> Check ()
> check_children_types types gram
>   | not (Set.null missing) =
>       throwErrorCheck $ Error_GramDesc_Missing missing
>   | not (Map.null wrong_types) =
>       throwErrorCheck $ Error_GramDesc_Wrong_Types (Map.keysSet wrong_types)
>   | otherwise = return ()
>  where
>    (!) = (Map.!)
>    missing = Set.difference children_nt (Map.keysSet gram)
>    children_nt = child_nt `Set.map` Map.keysSet types
>    wrong_types = Map.filterWithKey wrong_type types
>    wrong_type c t = fst (gram ! child_nt c) /= t -- well-defined if Set.null missing

> check_missing ::
>   Missing -> Check ()
> check_missing missing
>   | not (nullMissing missing) = throwErrorCheck $ Error_Missing missing
>   | otherwise = return ()

We check that the children have unique names for each production.

> check_grammar ::
>   Grammar -> Check ()
> check_grammar = traverse_ check_production

> check_production ::
>   Production -> Check ()
> check_production prod
>   | not (null dup) =
>       throwErrorCheck $ Error_Production_Duplicate_Children_Names dup prod
>   | otherwise = return ()
>   where
>     dup = duplicates (fst <$> prod_orphans prod)

Check the whole AG.

> check ::
>   GramDesc t -> InhDesc i -> SynDesc s -> Aspect -> Check (NonTerminal, PureAspect, Coalg)
> check g i s r = do
>   (root, grammar, gmap) <- check_gramDesc g
>   check_grammar grammar
>   let (check_aspect, ctx) = runAspect r
>   pure_asp <- check_aspect
>   check_missing (missing grammar ctx)
>   check_inh_unique i
>   check_inh_required i root (require_I ctx)
>   check_syn_ensured s grammar root (ensure_S ctx)
>   return (root, pure_asp, coalg gmap)

> run :: Typeable t =>
>   GramDesc t -> InhDesc i -> SynDesc s -> Aspect -> Check (t -> i -> s)
> run g i s a = do
>   (root, pure_asp, coalg) <- check g i s a
>   let sem = sem_coalg (Map.map sem_prod pure_asp) coalg root . toDynP g
>   return $ \x -> proj_S s . sem x . proj_I i

> coalg :: GramMap -> Coalg
> coalg = Map.map snd

** Running on a general tree
*** Checking a tree

Before we can execute an AG on a general tree, we must see if
the tree is compatible with the grammar.

> tree_gram :: InputTree -> Check Grammar
> tree_gram (Node prod cs ts)
>   | not (Set.null invalid_children) =
>       throwErrorCheck $ Error_Tree_Invalid_Children invalid_children prod
>   | not (Set.null missing_children) =
>       throwErrorCheck $ Error_Tree_Missing_Children missing_children prod
>   | not (Set.null invalid_terminals) =
>       throwErrorCheck $ Error_Tree_Invalid_Terminals invalid_terminals prod
>   | not (Set.null missing_terminals) =
>       throwErrorCheck $ Error_Tree_Missing_Terminals missing_terminals prod
>   | otherwise =
>       Map.foldr (\t ag_g -> liftM2 Set.union ag_g (tree_gram t))
>                 (return (Set.singleton prod)) cs
>   where
>     children = Map.keysSet cs
>     prod_cs = Set.fromList (prod_children prod)
>     ( invalid_children
>      , missing_children) = children `symdiff` prod_cs
>     terminals = Map.keysSet ts
>     prod_ts = prod_terminals prod
>     ( invalid_terminals
>      , missing_terminals) = terminals `symdiff` prod_ts

*** Checking the attributes

When we run the general tree we must provide a map for
inherited attributes. We check that all the required
attributes are defined.

> check_attrs ::
>   (Set Require_I -> ErrorMsg) ->
>   AttrSet I  -> NonTerminal -> Set Require_I -> Check ()
> check_attrs err attrs root req
>   | Set.null missing = return ()
>   | otherwise = throwErrorCheck $ err missing
>   where
>     missing = Set.difference req' attrs'
>     req' = Set.filter ((root ==) . constr_obj) req
>     attrs' = cstr `Set.map` attrs
>     cstr (Attribute a) = Constraint a root

*** Running an AG on a general tree

Abstract type for attributions.

> newtype Attrs k = Attrs {fromAttrs :: AttrMap k} deriving (Monoid)
> lookup_attrs :: (Typeable a) => Attr k a -> Attrs k -> Maybe a
> lookup_attrs a = lookupAttr a . fromAttrs

> infix 2 |=>
> single_attr, (|=>) :: Typeable a => Attr k a -> a -> Attrs k
> single_attr a x = Attrs $ singleAttr a x
> (|=>) = single_attr
> empty_attrs :: Attrs k
> empty_attrs = mempty
> merge_attrs :: Op (Attrs k)
> merge_attrs = mappend

> node ::
>   Production -> Child :-> InputTree -> Attrs T -> InputTree
> node p cs = Node p cs . fromAttrs

> runTree ::
>   Aspect -> NonTerminal -> InputTree -> Attrs I -> Check (Attrs S)
> runTree aspect root tree (Attrs inhattrs) = do
>   gram <- tree_gram tree
>   check_grammar gram
>   let (check_aspect, ctx) = runAspect aspect
>   pure_asp <- check_aspect
>   check_missing (missing gram ctx)
>   check_attrs Error_RunTree_Missing (Map.keysSet inhattrs) root (require_I ctx)
>   return $ Attrs $ unsafe_run pure_asp tree inhattrs

*** Semantics

> type SemTree = AttrMap I -> AttrMap S

> type SemProd = Child :-> SemTree -> AttrMap T -> SemTree

`sem_prod' ties the knot of attribute computation.
Note: we need to extend the domain of inh_children to cover
all the children of the current production.

> sem_prod :: PureRule -> SemProd
> sem_prod rule forest terminals inh = syn
>   where
>     (syn, inh_children) = rule (inh, syn_children, terminals)
>     syn_children = forest `applyMap` extended_inh
>     extended_inh = Map.union inh_children (constantMap emptyAttrs (Map.keysSet forest))

> unsafe_run :: PureAspect -> InputTree -> SemTree
> unsafe_run = sem_tree . Map.map sem_prod

`sem_tree' computes the iteration of the algebra on a tree.
This function is partial: it assumes everything has been
checked before.

> sem_tree :: Production :-> SemProd -> InputTree -> SemTree
> sem_tree alg = sem
>   where sem (Node p cs ts) = (alg Map.! p) (Map.map sem cs) ts

A Dynamic tree coalgebra

> type Coalg = NonTerminal :-> (Dynamic -> Match)


`sem_coalg' iterates the AG-algebra on a tree-coalgebra, this
function is partial: it assumes everything has been checked
before.

> sem_coalg ::
>   Production :-> SemProd ->
>   Coalg -> NonTerminal -> Dynamic -> SemTree
> sem_coalg alg coalg = sem
>   where
>     sem nt dyn = (alg Map.! prod) children terms
>       where
>         Match prod cmap terms = (coalg Map.! nt) dyn
>         children = Map.mapWithKey (\k d -> sem (child_nt k) d) cmap

** Computing an algebra
Running the AG is a catamorphism, sometimes it is useful to
know its algebra. An algebra for the attribute grammar has
the type:

    #+BEGIN_SRC haskell
    type Algebra = Production :-> SemProd
    type SemProd = Child :-> SemTree -> AttrMap T -> SemTree
    type SemTree = AttrMap I -> AttrMap S
    type SemProd = Child :-> SemTree -> AttrMap T -> SemTree
    #+END_SRC

The problem with that type is that it is unsafe.  To make it
safe, we must make the map `child :-> SemTree' abstract, as
well as the functions `AttrMap I -> AttrMap S', and collect
information about them: which inherited attributes are
required and which synthesized attributes are ensured for
each child, all of this in the context of a production.

The approach is very similar to the one for defining aspects
and gathering constraints, with `AlgM' playing the role of
the `A' monad, `SemTreeM' playing the role of the `R' monad,
and `AlgRule' playing the role of `AR' monoid.

> newtype AlgM a = AlgM {runAlgM :: ReaderT Child (ExceptT Error (Writer AlgCtx)) a}
>  deriving (Functor, Applicative, Monad, MonadReader Child, MonadError Error, MonadWriter AlgCtx)
> newtype SemTreeM a = SemTreeM {runSemTreeM :: Reader (AttrMap I) a}
>  deriving (Functor, Applicative, Monad, MonadReader (AttrMap I))
> newtype AlgRule a = AlgRule {runAlgRule :: AlgM (SemTreeM a)}
> newtype AlgInput = AlgInput (Check (Production, Child :-> AlgRule (AttrMap S)))

The context type is different we ensure synthesized
attributes for children rather than productions.

> data AlgCtx = AlgCtx
>   { algCtx_I :: Set Require_I
>   , algCtx_S :: Set (Constraint S Child)
>   }

> emptyAlgCtx = AlgCtx Set.empty Set.empty
> mergeAlgCtx (AlgCtx i s) (AlgCtx i' s') =
>   AlgCtx (Set.union i i') (Set.union s s')

> instance Monoid AlgCtx where
>   mempty = emptyAlgCtx
>   mappend = mergeAlgCtx

The previous types are abstract. We provide the following
primitives to build values.

> instance Applicative AlgRule where
>   pure x = AlgRule (pure (pure x))
>   AlgRule f <*> AlgRule x = AlgRule ((<*>) <$> f <*> x)
> instance Functor AlgRule where
>   fmap f x = pure f <*> x

> projI :: Typeable a => Attr I a -> AlgRule a
> projI a = AlgRule $ do
>  c <- ask
>  tell $ emptyAlgCtx { algCtx_I = cstr a (child_nt c) }
>  return $ do
>    is <- ask
>    return $ fromMaybe err $ lookupAttr a is
>   where
>     err = error $ "[BUG] projI: undefined attribute " ++ show a

> synAlg :: Typeable a => Attr S a -> Child -> AlgRule a -> AlgInput
> synAlg a c r =
>   AlgInput $ return (child_prod c, c |-> singleAttr a <$> r')
>  where
>   r' = AlgRule $ local (const c) (constraint >> runAlgRule r)
>   constraint = tell $ emptyAlgCtx { algCtx_S = cstr a c }

> emptyInput :: Production -> AlgInput
> emptyInput p = AlgInput $ return (p, Map.empty)

Note that mergeInput must check that both inputs are
compatible: the children in the map must be all siblings of
the same production.

> mergeInput :: AlgInput -> AlgInput -> AlgInput
> mergeInput (AlgInput x) (AlgInput y) = AlgInput $ do
>   (p, m) <- x
>   (p', m') <- y
>   when (p /= p') $ throwErrorCheck $ Error_Algebra_Different_Productions p p'
>   return (p, Map.unionWith mergeAlgRule m m')

`mergeAlgRule' is private, we go through two monads.

> mergeAlgRule :: Op (AlgRule (AttrMap S))
> mergeAlgRule (AlgRule x) (AlgRule y) = AlgRule $
>   liftM2 (liftM2 mergeAttrs) x y

 > runAlgebra :: Aspect -> AlgInput -> Attrs T -> Attrs I -> Check (Attrs S)
 > runAlgebra aspect input terminals inherited = do
 >   (p, rs) <- check_input input
 >   let (check_aspect, ctx) = runAspect aspect
 >   pure_asp <- check_aspect
 >   check_missing_alg (missing_alg ctx TODO)
 >   return empty_attrs

private

> check_input :: AlgInput -> Check (Production, Child :-> AlgRule (AttrMap S))
> check_input (AlgInput x) = do
>   (prod, rules) <- x
>   let (invalid_children, missing_children) =
>          symmetric set_diff (Map.keys rules) (prod_children prod)
>   unless (null invalid_children)
>     $ throwErrorCheck $ Error_Algebra_Invalid_Children invalid_children prod
>   unless (null missing_children)
>     $ throwErrorCheck $ Error_Algebra_Missing_Children missing_children prod
>   return (prod, rules)

* Literate Haskell with org-mode
The documentation part of this literate file is written in
`org-mode'.  To benefit from the enhanced navigation given by
this mode, you should do the following to setup emacs.

- install mmm-mode

  #+BEGIN_SRC elisp
  (package-install 'mmm-mode)
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
