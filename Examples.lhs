
> {-# LANGUAGE
>       TypeOperators
>     , GADTs
>     , DeriveDataTypeable
>     , GeneralizedNewtypeDeriving
>     , ScopedTypeVariables
>  #-}

> module Examples where
> import Data.Dynamic
> import Control.Applicative
> import AG

Type proxies (used in attribute definitions)

> pInt = Proxy :: Proxy Int
> pBTree = Proxy :: Proxy BTree
> pList :: Proxy a -> Proxy [a]
> pList _ = Proxy

Example Repmin

> data BTree = Fork BTree BTree | Leaf Int deriving Typeable
> data Root = Start BTree

Non-terminals

> btree = non_terminal "BTree"
> root = non_terminal "Root"

Productions

> start = production btree "Start" [startTree]
> fork = production btree "Fork" [leftTree, rightTree]
> leaf = production btree "Leaf" []

Children

> startTree = child start "startTree" btree
> leftTree = child fork "leftTree" btree
> rightTree = child fork "rightTree" btree

Attributes

> val = attr "val" T pInt -- leaf value (terminal)

> gmin = attr "gmin" I pInt
> locmin = attr "locmin" S pInt
> ntree = attr "ntree" S pBTree

Rules

> gminR = copyP gmin fork
>       & inh gmin startTree (startTree ! locmin)

List of the leaves

> tailf = attr "tail" I (pList pInt)
> flat = attr "flat" S (pList pInt)

> flattenR =
>   syns flat
>     [ start |- startTree ! flat
>     , leaf  |- (:) <$> ter val <*> par tailf
>     , fork  |- leftTree ! flat
>     ]
>   &
>   inhs tailf
>     [ rightTree |- par tailf
>     , leftTree  |- rightTree ! flat
>     , startTree |- par tailf
>     ]
