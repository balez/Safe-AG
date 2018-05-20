DSL for creating a context free grammar.

Note, we replace Core.production with a new function that
takes tuples of terminal attributes.

* Header
** GHC Options

> {-# LANGUAGE
>     FlexibleInstances
>   , TypeOperators
> #-}


** Module Exports

> module Grammar.SafeAG.CFG
>   ( Prodnchild((:@))
>   , ChildSpec((:::))
>   , production, prodnchild
>   ) where

** Module Imports

> import Grammar.SafeAG.Core hiding (production)
> import qualified Grammar.SafeAG.Core as Core (production)

> import Data.Typeable

* Terminal lists

> class Typeable a => TermList a where
>   termlist :: a -> Terminals

> instance TermList () where
>   termlist () = nilT

> instance Typeable a => TermList (Attr T a) where
>   termlist x = consT x (termlist ())

> instance (Typeable a, Typeable b) => TermList (Attr T a, Attr T b) where
>   termlist (x, y) = consT x (termlist y)

> instance (Typeable a, Typeable b, Typeable c) =>
>     TermList (Attr T a, Attr T b, Attr T c) where
>   termlist (x, y, z) = consT x (termlist (x, y))

> instance (Typeable a, Typeable b, Typeable c, Typeable d) =>
>     TermList (Attr T a, Attr T b, Attr T c, Attr T d) where
>   termlist (a, b, c, d) = consT a (termlist (b, c, d))

> instance (Typeable a, Typeable b, Typeable c, Typeable d, Typeable e) =>
>     TermList (Attr T a, Attr T b, Attr T c, Attr T d, Attr T e) where
>   termlist (a, b, c, d, e) = consT a (termlist (b, c, d, e))

> instance (Typeable a, Typeable b, Typeable c, Typeable d, Typeable e, Typeable f) =>
>     TermList (Attr T a, Attr T b, Attr T c, Attr T d, Attr T e, Attr T f) where
>   termlist (a, b, c, d, e, f) = consT a (termlist (b, c, d, e, f))

> production :: TermList a => NonTerminal -> Name -> Children -> a -> Production
> production nt p cs ts = Core.production nt p cs (termlist ts)


* Datatypes

> infix 3 :@
> infix 1 :::

> data Prodnchild = Production :@ Children

> data ChildSpec = Name ::: NonTerminal

* Semantics

> prodnchild :: TermList t =>
>   NonTerminal -> Name -> [ChildSpec] -> t -> Prodnchild

> prodnchild nt name children ts = prod :@ cs
>   where
>     prod = production nt name cs ts
>     cs = map child_spec children
>     child_spec (name ::: nt) =
>       child prod name nt




* Local variables for emacs
Local Variables:
mode: org
eval: (org-indent-mode -1)
eval: (mmm-mode)
eval: (mmm-ify-by-class 'literate-haskell-bird)
eval: (local-set-key (kbd "<XF86MonBrightnessDown>") 'mmm-parse-buffer)
compile-command: "cd ../..; ghc Grammar/SafeAG/CFG.lhs"
End:
