TODO
- raise kind errors
- correct the context simplification
- better syntax to create AG
- running the attribute grammar
- github
- (for later) Indexed Tree with phantom variables to reflect the nt, prod, children.


IMPORTANT:
- when using the library primitives, the user should never
  SEE any `Dynamic', always concrete types.

EDSL for attribute grammars in Haskell inspired by De Moor's
design.  With runtime typechecking. It is the dynamic version
of the AG a la carte design.  Runtime typechecking is to be
contrasted with dynamic typing in that we do the typechecking
at runtime once and for all, whereas dynamic typing involves
doing testing the types every time a function is used. With
the possibility to fail if the type mismatch. However with
runtime typechecking, if a function passes the tests, we have
the certainty that no type error will be the cause for
failure when executing that function.

The approach involves a combination of static and runtime
typechecking: the type of attributes and their kind
(inherited, synthesized, or terminals) is checked
statically. But the completeness of the grammar is checked at
runtime.

* We want to collect type informations on rules before even
computing them, so that the whole AG can be typechecked
before it is being run.  In order to do that, we use a monad,
that writes constraints and that read the input of the rules
(a family). But since we want to collect before computing,
the writer must come before the reader. This means we do not
have access to the input types.

* Could we run the AG in a typed way?

Rather than run the AG on the general tree type.

 > type Partial a = Either Error a -- success or failure monad
 
 > check :: spec t i s -> Rule -> Partial (AG t i s)
 > run :: AG t i s -> t -> i -> s

The spec should say
- The grammar (set of productions)
- The set of attributes (packaged with their types) and their domain (set of non-terminals)

  A finite map from attributes to non-terminals will contain
  the necessary information (since we can obtain the set of the
  keys from the map)

Thus:

 > type Grammar = Set Production
 > type Domain = Attribute :-> Set NonTerminal
 > type AGSpec = (Grammar, Domain)

In the typed version, in addition we must build (total) conversions between
- t and the tree type,
- i,s and the AttrMap type.

To specify i and s, we must keep track of the attributes that
they will be using and build conversion functions
(i -> AttrMap) and (AttrMap -> s).

`AttrSpec' is a list of attributes with existential
quantification over the attribute type.

 > type AttrSpec = [Attribute]

For the synthesized attributes the following interface is enough.
(AttrSpec, InhSpec, SynSpec, Attrs, Attribute are all abstract types)

 > type SynSpec s = Writer AttrSpec (AttrMap -> s)
 > instance Applicative SynSpec
 > project :: Typeable a => Attr a -> SynSpec a

For inherited attributes, the following interface is enough.

 > type InhSpec i = Writer AttrSpec (i -> AttrMap)
 > embed :: Attr a -> (i -> a) -> InhSpec i
 > (#) :: InhSpec i -> InhSpec i -> InhSpec i

example:

 > data I = I { a :: Int, b :: Bool }
 > data S = S { c :: String, d :: Float }
 >
 > count :: Attr Int
 > flag :: Attr Bool
 > output :: Attr String
 > speed :: Attr Float
 >
 > specI = embed count a # embed flag b :: InhSpec I
 > specS = S <$> project output <*> project speed :: SynSpec S


Specifying that the tree corresponds to the grammar and how
it is mapped is very hard.  In the general case we use a GADT
to capture the context free grammar.  We must check that the
tree type is a subset of the context free grammar.  That for
each constructor of the tree there is a corresponding
production and that the children match.

In the simple case when there is only one non-terminal, we
need to tell which production corresponds to which
constructor, and at the same time which of the children of the constructor are:

 > deconstruct :: t -> ([t], Production)

We need to collect the list of all possible productions in
the range of `deconstruct'.  But we cannot evaluate
deconstruct. (we would need to evaluate it for an infinite
number of input in order to collect the range).
Can we use the type system to constrain the range of deconstruct?

If we accept to build deconstruct by gluing partial pieces,
putting the responsability of termination in the users hand,
then we can proceed as follows:

 > type Constr t = t -> Maybe (Production, [t])
 > type TreeSpec t = Writer [Production] [Constr t]
 > instance Monoid TreeSpec
 > constr = Production -> (t -> Maybe [t]) -> TreeSpec t
 > glue :: [Constr t] -> t -> Tree

Example

 > node :: Production
 > leaf :: Production
 
 > nodeC (Node l r) = Just ([l,r])
 > nodeC _ = Nothing
 
 > leafC (Leaf x) = Just []
 > leafC _ = Nothing
 
 > treeC :: Constr t
 > treeC = constr node nodeC <|> constr leaf leafC

Now we didn't consider terminals. Terminals are embedded as
attributes of Val nodes in the tree. This again requires us
to check that the attributes are compatible with the
rules. We reuse the InhSpec type that specifies functions of
type `i -> AttrMap`.

 > type Constr t = t -> Maybe (Production, [t], AttrMap)
 > type TreeSpec t = Writer ([Production],[Attribute]) [Constr t]
 > instance Monoid TreeSpec
 > constr = Production -> InhSpec i -> (t -> Maybe ([t], i)) -> TreeSpec t
 > glue :: [Constr t] -> t -> Tree

Now in order to constrain the number of children for each
production, we can use a vector type, so the combination of
static check and runtime typechecking ensures that we will
always be constructing valid production.

 > constr = Production -> Nat n -> InhSpec i -> (t -> Maybe (Vec n t, i)) -> TreeSpec t

The function (nat :: Nat n -> Int) allows us to check that
the vector has the same number of elements as the
production's children.

The last generalisation that we want is map families of
recursive types to a context free grammar. This involves
using GADTs. Now to capture the list of children, we not only
need their number, but their type. Thus we use a heterogenous
list indexed by the type level list of the element's types.

 > data HList t ks where
 >   HNil :: HList '[]
 >   HCons :: t k -> HList t ks -> HList (k ': ks)

We must capture what a type level list is, in order to compute its length.

 > data TList ks where
 >   TNil :: TList '[]
 >   TCons :: Proxy k -> TList ks -> TList (k ': ks)

 > constr = Production -> TList ks -> InhSpec i -> (t k -> Maybe (HList t ks, i)) -> TreeSpec t


> {-# LANGUAGE
>       TypeOperators
>     , GADTs
>     , DeriveDataTypeable
>     , GeneralizedNewtypeDeriving
>     , StandaloneDeriving
>  #-}

> module AG where
> import Control.Applicative
> import Control.Monad.Except
> import Control.Monad.Writer.Strict
> import Control.Monad.Reader
> import Data.Dynamic
> import qualified Data.Set as Set
> import Data.Set (Set)
> import Data.List (nub)
> import qualified Data.Map as Map
> import Data.Traversable
> import Unknown

http://hackage.haskell.org/package/base-4.9.0.0/docs/GHC-Stack.html

> cst2 r x y = r
> cst3 r x y z = r
> fromJust (Just x) = x
> filterJust xs = [ x | Just x <- xs ]

 > import Data.Map ((!))

Map operations

> infixr 1 :->
> type (:->) = Map.Map


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

Set operations

> allSet :: (a -> Bool) -> Set a -> Bool
> allSet p = Set.foldr (\x b -> p x && b) True

An attribute grammar has two elements: a context free grammar
describing a language, or equivalently, the type of its parse
tree.  And semantic rules, that define the value of
attributes for each non-terminal of the grammar, (each node
of the tree).

We start by defining a general tree type. The tree is parameterised with
node labels, which are simply the production in the case of the input tree,
but can also be paired with attributes in the case of a decorated tree.
The `Val' constructor introduces the non-terminal data.

> data Tree n = Node n (Child :-> Tree n) | Val AttrMap
> type InputTree = Tree Production
> type DecoratedTree = Tree (Production, AttrMap)


A decorated r
where the `Val' constructor contains the terminal data. and

> type Name = String
> type NonTerminalName = Name
> type ProdName = (NonTerminal, Name)
> type ChildName = (ProdName, Name)
> type AttrName = Name

Note that the child doesn't link to the production, because
that would cause a cycle and thus equality on children would
diverge. (And we need equality)
During typechecking we will only keep track about the
ProdName anyways.

> newtype NonTerminal = NT NonTerminalName deriving (Eq, Ord)

> data Production = Production
>   { prod_name :: ProdName
>   , prod_children :: Children }
>   deriving (Eq, Ord)

> data Child = Child
>   { child_name :: ChildName
>   , child_nt ::  NonTerminal }
>   deriving (Eq, Ord)

> type Children = [Child]

> non_terminal = NT

> production :: NonTerminal -> Name -> Children -> Production
> production n p cs = Production (n,p) cs

> child :: Production -> Name -> NonTerminal -> Child
> child p c n = Child (prod_name p, c) n

> prod_nt = fst . prod_name
> child_prod = fst . child_name

A grammar can be given by a set of production.
Also note that not all values of type `Grammar' are valid grammars:
we need to check that the productions are all valid.

> type Grammar = Set Production

Later we can make the return type convey error information.

> valid_grammar :: Grammar -> Bool
> valid_grammar = all valid_production . Set.toList

Later we can make the return type convey error information.

> valid_production :: Production -> Bool
> valid_production p = all valid_child (prod_children p)
>   where valid_child c = child_prod c == prod_name p

> gram_children :: Grammar -> Set Child
> gram_children gram =
>   Set.foldr
>     (\cs -> Set.union (Set.fromList cs))
>     Set.empty
>     (Set.map prod_children gram)

Attribute kinds: I, S, T

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

heterogenous equality on kinds

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

> data Attr m a = Attr Name (Kind m)

> attr :: Typeable a => Name -> Kind m -> p a -> Attr m a
> attr n k _ = Attr n k

> data Attribute where
>   Attribute :: Typeable a => Attr k a -> Attribute

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

> eqAttr :: (Typeable a, Typeable a') => Attr k a -> Attr k' a' -> Bool
> eqAttr x y = Attribute x == Attribute y

> compareAttr :: (Typeable a, Typeable a') => Attr k a -> Attr k' a' -> Ordering
> compareAttr x y = Attribute x `compare` Attribute y

An attribution is a finite map from attribute name to values.
Note: the use of Dynamics prevents us from having polymorphic
attributes.

> type AttrMap = Attribute :-> Dynamic
> emptyAttrs :: AttrMap
> emptyAttrs = Map.empty
> mergeAttrs :: Op AttrMap
> mergeAttrs = Map.union
> lookupAttr :: Typeable a => Attr k a -> AttrMap -> Maybe Dynamic
> lookupAttr x = Map.lookup (Attribute x)
> projAttr :: Typeable a => AttrMap -> Attr k a -> Maybe Dynamic
> projAttr = flip lookupAttr

Parent and children and terminal attributions.

> type TerminalAttrs = AttrMap
> type ParentAttrs = AttrMap
> type ChildrenAttrs = Child :-> AttrMap
> emptyChildrenAttrs :: ChildrenAttrs
> emptyChildrenAttrs = Map.empty
> mergeChildrenAttrs :: Op ChildrenAttrs
> mergeChildrenAttrs x y =
>   Map.unionWith mergeAttrs x y

A Family of attribution: for the parent of the node and for
the children.  (Not all children need to be given an
attribute). Note that the terminal attributes are only used
as input. In the output, the terminal map will always be empty.

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

The domain of an attribute states for which non-terminals it
should be defined.

> type Domain = Attribute :-> Set NonTerminal

A domain together with a context free grammar, constitute the
signature of an attribute grammar: we should be able to tell
if a given implementation is compatible or not with that signature.

> type AGSig = (Grammar, Domain)

In order to check that an AG implementation is compatible with a signature,
we must collect information about the rules:

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

> newtype A a = A {runA :: ReaderT Production (ExceptT Error (Writer Context)) a} -- the aspect monad
>   deriving (Functor, Applicative, Monad, MonadReader Production, MonadError Error, MonadWriter Context)

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

Rule is abstract, only operations are the monoid

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

> concatRules = foldl mergeRule emptyRule

Errors in a rule.

  `Error_Child c p' :
     when child `c' was used in the context of the production `p`
     which doesn't list this child.

> data Error =
>   Error_Child Child Production

* Constraints, Contexts

Note that the use of the kind and the phantom type on
Attributes ensures that attributes can only be used with
their given kind and type. Therefore we do not need to check
attribute types. And the use of children lists in production
ensures that children can only be used in their given
production.

Therefore we only need to keep track of attributes that are
used (required) and attributes that are defined (ensured).

> data Ensure k where
>   Ensure_Child :: Typeable a => Child -> Attr I a -> Ensure I
>   Ensure_Parent :: Typeable a => Production -> Attr S a -> Ensure S

> ensured_child :: Ensure I -> Child
> ensured_child (Ensure_Child c a) = c

> ensured_prod :: Ensure S -> Production
> ensured_prod (Ensure_Parent p a) = p

> data Constraint k where
>   Constraint :: Typeable a => NonTerminal -> Attr k a -> Constraint k

> type Require = Constraint

> instance Eq (Ensure k) where
>   e == e'  =  compare e e' == EQ

> instance Eq (Constraint k) where
>   r == r'  =  compare r r' == EQ

> instance Ord (Ensure k) where
>   compare (Ensure_Child c a) (Ensure_Child c' a')
>     = lexicographic (compare c c') (compareAttr a a')
>   compare (Ensure_Parent p a) (Ensure_Parent p' a')
>     = lexicographic (compare p p') (compareAttr a a')
>   compare (Ensure_Child _ _) _ = LT
>   compare _ _ = GT

> instance Ord (Constraint k) where
>   compare (Constraint n a) (Constraint n' a')
>     = lexicographic (compare n n') (compareAttr a a')

> ensure_constraint :: Ensure k -> Constraint k
> ensure_constraint (Ensure_Child c a) =
>   Constraint (child_nt c) a
> ensure_constraint (Ensure_Parent p a) =
>   Constraint (prod_nt p) a

Contexts are modelled with sets of constraints. They form a
monoid, therefore the Writer monad uses the mappend function
to update the constraints. Note that contexts are cannot be
more simplified.

The terminals constraints are always required and never
ensured: those constraints will be used when checking that
the input tree is well-formed.

> data Context = Ctx
>   { ensure_children   :: Set (Ensure I)
>   , ensure_parents    :: Set (Ensure S)
>   , require_children  :: Set (Require S)
>   , require_parents   :: Set (Require I)
>   , require_terminals :: Set (Require T)
>   }

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

`nullCtx` is true iff the context is empty.

> nullCtx (Ctx ec ep rc rp rt) =
>   Set.null ec
>   && Set.null ep
>   && Set.null rc
>   && Set.null rp
>   && Set.null rt

There is no invalid context, and no redundent
constraints. The only thing we can do is to check whether a
context is complete: i.e. all `require` constraints are met by
matching `ensure` constraints.

> complete_ctx ::
>   Grammar -> Context -> Bool
> complete_ctx g c =
>   complete S g (ensure_parents c) (require_children c)
>   && complete I g (ensure_children c) (require_parents c)

> complete ::
>   Kind k -> Grammar -> Set (Ensure k) -> Set (Require k) -> Bool
> complete k g e =
>   allSet (check_require k g e)

> check_require ::
>   Kind k -> Grammar -> Set (Ensure k) -> Require k -> Bool
> check_require S =
>   check_require_with prod_nt ensured_prod id S
> check_require I =
>   check_require_with child_nt ensured_child gram_children I
> check_require T = cst3 True -- we cannot check those constraints yet.

> check_require_with :: (Ord a) =>
>   (a -> NonTerminal) ->
>   (Ensure k -> a) ->
>   (Grammar -> Set a) ->
>   Kind k -> Grammar -> Set (Ensure k) -> Require k -> Bool
> check_require_with proj ensure_elem list_elem k gram ensure
>   r@(Constraint n a) =
>     Set.null $ Set.difference matching ensured
>   where
>     matching =
>       Set.filter (\x -> proj x == n) (list_elem gram)
>     ensured =
>       Set.map ensure_elem $
>         Set.filter (\e -> ensure_constraint e == r) ensure

The primitive ways to update the context are through the
require_* and ensure_* functions.

> tell_parent f = current_production >>= tell . f

Generate errors if the child is not valid in the current production.

> assert_child c = do
>   p <- current_production
>   unless (c `elem` prod_children p)
>     $ throwError (Error_Child c p)

> require_child ::
>   Typeable a => Child -> Attr S a -> A ()
> require_child c a = do
>   assert_child c
>   tell $ emptyCtx { require_children =
>                       Set.singleton (Constraint (child_nt c) a) }

> ensure_child ::
>   Typeable a => Child -> Attr I a -> A ()
> ensure_child c a = do
>   assert_child c
>   tell $ emptyCtx { ensure_children =
>                       Set.singleton (Ensure_Child c a) }

> require_parent ::
>   Typeable a => Attr I a -> A ()
> require_parent a = tell_parent $ \p ->
>   emptyCtx { require_parents =
>                 Set.singleton (Constraint (prod_nt p) a) }

> ensure_parent ::
>   Typeable a => Attr S a -> A ()
> ensure_parent a = tell_parent $ \p ->
>   emptyCtx { ensure_parents =
>                 Set.singleton (Ensure_Parent p a) }

> require_terminal ::
>   Typeable a => Attr T a -> A ()
> require_terminal a = tell_parent $ \p ->
>   emptyCtx { require_terminals =
>                 Set.singleton (Constraint (prod_nt p) a) }

The primitives to build aspects project attributes from either
the parent, a child of the production or the terminal child.
Those primitive generate `Require' constraints.

The `Maybe' versions of `chi', `par' and `ter' do not add any
constraints: their success or failure is captured by the
Maybe monad at runtime.

Children attribute

> (?), chiM :: Typeable a => Child -> Attr S a -> AR (Maybe a)
> (?) c a = AR $ return $ do
>   cs <- asks childrenAttrs
>   let md = Map.lookup c cs >>= lookupAttr a
>   return $ fromJust . fromDynamic <$> md
> chiM = (?)

Parent attribute

> parM :: Typeable a => Attr I a -> AR (Maybe a)
> parM a = AR $ return $ do
>  ps <- asks parentAttrs
>  return $ fromJust . fromDynamic <$> lookupAttr a ps

Terminal attribute

> terM :: Typeable a => Attr T a -> AR (Maybe a)
> terM a = AR $ return $ do
>   ts <- asks terminalAttrs
>   return $ fromJust . fromDynamic <$> lookupAttr a ts

The strict versions are all instances of the following:

> strictProj :: Typeable a =>
>   (Attr k a -> AR (Maybe a)) ->   -- the maybe operation
>   (Attr k a -> A ()) ->           -- the constraint
>   Attr k a -> AR a
> strictProj get require a = AR $ do
>   require a
>   rma <- runAR (get a)
>   return (fromJust <$> rma) -- safe coercion after we added the constraint

> infix 9 !
> (!), chi :: Typeable a => Child -> Attr S a -> AR a
> (!) c = strictProj (c ?) (require_child c)
> chi = (!)

> par :: Typeable a => Attr I a -> AR a
> par = strictProj parM require_parent

> ter :: Typeable a => Attr T a -> AR a
> ter = strictProj terM require_terminal

Inherited attributes are defined for a specific child of a
production.  The production is determined by the Child.

> inh :: Typeable a => Attr I a -> Child -> AR a -> Rule
> inh a c r = Rule $
>    ensure_child c a `bindAR_`
>    (fam <$> r)
>   where
>     fam x = emptyFam { childrenAttrs =
>                           c |-> Attribute a |-> toDyn x }

> inhs :: Typeable a => Attr I a -> [(Child, AR a)] -> Rule
> inhs a = foldl (\rs (c,r) -> rs & inh a c r) emptyRule

Synthesized attributes are defined for the parent of a production.

> syn :: Typeable a => Attr S a -> Production -> AR a -> Rule
> syn a p r = Rule $ AR $ do
>   r' <- local (const p) (ensure_parent a >> runAR r)
>   return $ fam <$> r'
>  where
>   fam x = emptyFam { parentAttrs = Attribute a |-> toDyn x }

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
