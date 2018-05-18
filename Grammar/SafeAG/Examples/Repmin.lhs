* Header
** lhs2TeX

%include lhs2TeX.fmt
%include applicative.fmt

** GHC Extensions

> {-# LANGUAGE
>       TypeOperators
>     , GADTs
>     , DeriveDataTypeable
>     , GeneralizedNewtypeDeriving
>     , ScopedTypeVariables
>     , LambdaCase
>     , TemplateHaskell
>  #-}

** Module Imports

> module Grammar.SafeAG.Examples.Repmin where
> import Data.Dynamic (Typeable, Proxy(..))
> import qualified Data.Set as Set
> import qualified Data.Map as Map
> import Control.Applicative
> import GHC.Stack
> import Grammar.SafeAG
> import Grammar.SafeAG.TH.Idiom (idiom)
> import Grammar.SafeAG.TH.Applicative

* Type proxies (used in attribute definitions)

> pInt = Proxy :: Proxy Int
> pBTree = Proxy :: Proxy BTree
> pList :: Proxy a -> Proxy [a]
> pList _ = Proxy

* Binary tree

> data BTree = Fork BTree BTree | Leaf Int
>            deriving (Show, Typeable)
> data Root = Start BTree
>            deriving (Show, Typeable)

* Context free grammar

** Using the primitives for grammar definition
*** Non-terminals

 > btree = non_terminal "BTree"
 > root = non_terminal "Root"

*** Productions

 > start = production root "Start" [startTree] ()
 > fork = production btree "Fork" [leftTree, rightTree] ()
 > leaf = production btree "Leaf" [] val

*** Children

 > startTree = child start "startTree" btree
 > rightTree = child fork "rightTree" btree
 > leftTree = child fork "leftTree" btree

** Simultaneous definition of children and productions
*** Non-terminals

> btree = non_terminal "BTree"
> root = non_terminal "Root"

*** Productions

> start :@ [startTree] = prodnchild root
>   "Start" ["startTree" ::: btree] ()
> fork :@ [leftTree, rightTree] = prodnchild btree
>   "Fork" ["leftTree" ::: btree, "rightTree" ::: btree] ()
> leaf :@ [] = prodnchild btree "Leaf" [] val

** Using the DSL -- deprecated

The same grammar is written as follows:

 > [  root  ::= start :@ [startTree]
 >  , btree ::= fork  :@ [leftTree, rightTree]
 >           :| leaf  :@ []
 >  ] = grammar $
 >     [ "Root"  ::= "Start" :@ ["startTree" ::: btree] :& x
 >     , "BTree" ::= "Fork"  :@ ["leftTree"  ::: btree
 >                              ,"rightTree" ::: btree] :& x
 >                :| "Leaf"  :@ [] :& val & x
 >     ]
 >   where x = nilT
 >         (&) = consT

*** A non-terminal can be extended later with new productions:

> -- cons :@ [tailTree] =
> --   productions $
> --     btree ::= "Cons" :@ ["tailTree" ::: btree] :& nilT
>

** Using GramDesc

In addition to define independent grammars, we associate
them to a concrete type, this will allow
us to run AG safely.

> rootDesc =
>   root |=
>    [ start |=
>        [ startTree |= \(Start x) -> Just x
>        ] & []
>    ]
>  |||
>   btree |=
>    [ fork |=
>        [ leftTree  |= \case {Fork x _ -> Just x; _ -> Nothing}
>        , rightTree |= \case {Fork _ x -> Just x; _ -> Nothing}
>        ]
>        & []
>    , leaf |= [] & [val |= \case {Leaf x -> Just x; _ -> Nothing}]
>    ]

> repminI = emptyInDesc
> repminS = project ntree

** Grammar

> rootG = Set.fromList [start,fork,leaf]

* Attributes

> val = attr T "val" pInt -- leaf value (terminal)

> gmin = attr I "gmin" pInt
> locmin = attr S "locmin" pInt
> ntree = attr S "ntree" pBTree

* Rules
** Repmin
Remember the priority of merging is left to right, so copy
must be given last.

> repminA = gminA # locminA # ntreeA

> gminA = inhs gmin
>   [ startTree |- startTree!locmin ]
>   # copyP gmin fork

> locminA = syns locmin
>   [ leaf  |- ter val
>   , start |- startTree!locmin
>   ]
>   # collectAll locmin minimum fork

> ntreeA = syns ntree
>   [ leaf  |- ⟦ Leaf ⟨par gmin⟩ ⟧
>   , fork  |- ⟦ Fork ⟨leftTree!ntree⟩ ⟨rightTree!ntree⟩ ⟧
>   , start |- startTree!ntree
>   ]

Try
 >>> missing rootG (context ntreeA)
 >>> missing rootG (context repminA)

*** Running

> repminAG = (\f r -> f r ()) <$> run rootDesc repminI repminS repminA
> repmin x = case repminAG of
>   Left err -> print err
>   Right f -> print $ f x

> repminTree = runTreeAG repminA ntree

> runlocmin x = case run rootDesc mempty (project locmin) locminA of
>   Left err -> print err
>   Right f -> print $ f x ()

** List of the leaves

> tailf = attr I "tail" (pList pInt)
> flat = attr S "flat" (pList pInt)

> flattenA = flatA # tailA

> flatA = syns flat
>   [ start |- startTree!flat
>   , leaf  |- ⟦⟪ ter val : par tailf ⟫⟧
>   , fork  |- leftTree!flat
>   ]

> tailA = inhs tailf
>   [ rightTree |- par tailf
>   , leftTree  |- rightTree!flat
>   , startTree |- ⟦ [] ⟧
>   ]

*** Testing
    Try
 > missing rootG (context tailA)
 > missing rootG (context flattenA)

Trying the error system

> badChild = syn flat leaf (leftTree!flat)

 Try
 > check_rule badChild

*** Running

> flattenI = emptyInDesc
> flattenS = project flat

> flattenAG = (\f r -> f r ()) <$> run rootDesc flattenI flattenS flattenA

> flatten x = case flattenAG of
>   Left err -> print err
>   Right f -> print $ f x

> flattenTree = runTreeAG flattenA flat

** Height

> height = attr S "height" pInt
> heightA = syns height
>   [ start |- startTree!height ]
>   # collectPs height (\hs -> 1 + max0 hs) [fork, leaf]
>  where max0 = foldl max 0

> runheight x = case run rootDesc mempty (project height) heightA of
>   Left err -> print err
>   Right f -> print $ f x ()

* Main

> main = do
>   runlocmin example
>   runheight example
>   repmin example
>   flatten example

* Input Tree
** BTree

> example = s ((l 3 * l 1) * (l 4 * (l 1 * l 2)))
>   where s = Start
>         (*) = Fork
>         l = Leaf

** General Tree

> exampleTree = s ((l 3 * l 1) * (l 4 * (l 1 * l 2)))
>   where s x = node start (startTree |-> x) mempty
>         x * y = node fork (leftTree |-> x \/ rightTree |-> y) mempty
>         l x = node leaf Map.empty (val |=> x)

* Testing the general trees

> runTreeAG ag attr x = case runTree ag root x mempty of
>   Left err -> putStr $ prettyError $ err
>   Right s -> print $ s ! attr
>  where m ! x = fromJust $ lookup_attrs x m
>        fromJust (Just x) = x

* Testing the error messages

** duplicated rule

> ntree2A = repminA # syn ntree leaf (pure (Leaf 0))

** invalid child

> locmin2 = syn locmin start (leftTree!locmin)

* Local variables for emacs
Local Variables:
mode: org
eval: (org-indent-mode -1)
eval: (mmm-ify-by-class 'literate-haskell-bird)
eval: (local-set-key (kbd "<XF86MonBrightnessDown>") 'mmm-parse-buffer)
compile-command: "lhs2TeX --newcode Repmin.lhs > Repmin.hs && cd ../../..; ghc Grammar/SafeAG/Examples/Repmin.hs"
End:
