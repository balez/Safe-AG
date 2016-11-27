
> {-# LANGUAGE
>       TypeOperators
>     , GADTs
>     , DeriveDataTypeable
>     , GeneralizedNewtypeDeriving
>     , ScopedTypeVariables
>  #-}

> module Examples where
> import Data.Dynamic
> import qualified Data.Set as Set
> import qualified Data.Map as Map
> import Control.Applicative
> import AG

Type proxies (used in attribute definitions)

> pInt = Proxy :: Proxy Int
> pBTree = Proxy :: Proxy BTree
> pList :: Proxy a -> Proxy [a]
> pList _ = Proxy

Example Repmin

> data BTree = Fork BTree BTree | Leaf Int
>            deriving (Show, Typeable)
> data Root = Start BTree

 Non-terminals
 
 > btree = non_terminal "BTree"
 > root = non_terminal "Root"
 
 Productions
 
 > start = production btree "Start" [startTree] nilT
 > fork = production btree "Fork" [leftTree, rightTree] nilT
 > leaf = production btree "Leaf" [] (val `consT` nilT)
 
 Children
 
 > startTree = child start "startTree" btree
 > leftTree = child fork "leftTree" btree
 > rightTree = child fork "rightTree" btree
 
 
Using the DSL, the same grammar is written as follows:

> [  root  ::= start :@ [startTree]
>  , btree ::= fork  :@ [leftTree, rightTree]
>           :| leaf  :@ []
>  ] = grammar $
>     [ "Root"  ::= "Start" :@ ["startTree" ::: btree] :& x
>     , "BTree" ::= "Fork"  :@ ["leftTree"  ::: btree
>                              ,"rightTree" ::: btree] :& x
>                :| "Leaf"  :@ [] :& x --val & x
>     ]
>   where x = nilT
>         --(&) = consT

A non-terminal can be extended later with new productions:

> cons :@ [tailTree] =
>   productions $
>     btree ::= "Cons" :@ ["tailTree" ::: btree] :& nilT

Attributes

> val = attr "val" T pInt -- leaf value (terminal)

> gmin = attr "gmin" I pInt
> locmin = attr "locmin" S pInt
> ntree = attr "ntree" S pBTree

Grammar

> btreeG = Set.fromList [start,fork,leaf]


Rules

Remember the priority of merging is left to right, so copy
must be given last.

> repminR = gminR & locminR & ntreeR

> gminR = inh gmin startTree (startTree!locmin)
>         & copyP gmin fork

> locminR = syns locmin
>           [ leaf |- ter val
>           , start |- startTree!locmin]
>   & collectAll locmin minimum fork

> ntreeR = syns ntree
>   [ leaf |- liftA Leaf (par gmin)
>   , fork |- liftA2 Fork (leftTree!ntree) (rightTree!ntree)
>   , start |- startTree!ntree
>   ]

 Try
 > missing btreeG (context ntreeR)
 > missing btreeG repminR


List of the leaves

> tailf = attr "tail" I (pList pInt)
> flat = attr "flat" S (pList pInt)

> flattenR = flatR & tailR

> flatR = syns flat
>     [ start |- startTree!flat
>     , leaf  |- (:) <$> ter val <*> par tailf
>     , fork  |- leftTree!flat
>     ]

> tailR =
>   inhs tailf
>     [ rightTree |- par tailf
>     , leftTree  |- rightTree!flat
>     , startTree |- par tailf
>     ]

 Try
 > missing btreeG (context tailR)
 > missing btreeG flattenR

 > let (Right r,c) = runRule repminR
 > in unsafe_run r example emptyAttrs

Trying the error system

> badChild = syn flat leaf (leftTree!flat)

 Try
 > checkRule badChild

Input Tree

> example = s ((l 3 * l 1) * (l 4 * (l 1 * l 2)))
>   where s x = Node start (startTree |-> x) emptyAttrs
>         x * y = Node fork (leftTree |-> x \/ rightTree |-> y) emptyAttrs
>         l x = Node leaf Map.empty (val |=> x)
