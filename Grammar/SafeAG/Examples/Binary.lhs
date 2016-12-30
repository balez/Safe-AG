The attribute grammar for binary number is the example given
in Knuth original paper "Semantics of Context Free Languages".

* Header
** GHC Extensions

> {-# LANGUAGE
>       TypeOperators
>     , GADTs
>     , DeriveDataTypeable
>     , GeneralizedNewtypeDeriving
>     , ScopedTypeVariables
>     , LambdaCase
>  #-}

** Module Imports

> module Grammar.SafeAG.Examples.Binary where
> import Data.Proxy (Proxy(..))
> import qualified Data.Set as Set
> import qualified Data.Map as Map
> import Control.Applicative
> import GHC.Stack
> import Grammar.SafeAG

* Grammar

> [  number   ::= integer    :@ [digits]
>              :| fraction   :@ [pos, neg]
>  , list     ::= last       :@ [last_bit]
>              :| snoc       :@ [snoc_list, snoc_bit]
>  , bit      ::= zero       :@ []
>              :| one        :@ []
>  ] = grammar $
>  [ "Number" ::= "Integer"  @: [ "digits"    ::: list ]
>              :| "Fraction" @: [ "pos"       ::: list
>                               , "neg"       ::: list ]
>  , "List"   ::= "Last"     @: [ "last_bit"  ::: bit  ]
>              :| "Snoc"     @: [ "snoc_list" ::: list
>                               , "snoc_bit"  ::: bit  ]
>  , "Bit"    ::= "Zero"     @: []
>              :| "One"      @: []
>  ]
>  where
>   x @: y = x :@ y :& nilT

* Local variables for emacs

Local Variables:
mode: org
eval: (org-indent-mode -1)
eval: (mmm-ify-by-class 'literate-haskell-bird)
eval: (local-set-key (kbd "<XF86MonBrightnessDown>") 'mmm-parse-buffer)
compile-command: "cd ../../..; ghc Grammar.SafeAG.Examples.Binary"
End:
