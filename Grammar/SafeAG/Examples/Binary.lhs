The attribute grammar for binary number is the example given
in Knuth original paper "Semantics of Context Free Languages".

* Header
** lhs2TeX

%include lhs2TeX.fmt
%include idiom.fmt

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

> module Grammar.SafeAG.Examples.Binary where
> import Data.Proxy (Proxy(..))
> import Data.Ratio
> import Control.Applicative
> import Grammar.SafeAG
> import Grammar.SafeAG.Examples.Idiom (idiom)

* Grammar

> [  number   ::= integer    :@ [digits]
>              :| fraction   :@ [pos, neg]
>  , list     ::= single     :@ [single_bit]
>              :| snoc       :@ [snoc_list, snoc_bit]
>  , bit      ::= zero       :@ []
>              :| one        :@ []
>  ] = grammar $
>  [ "Number" ::= "Integer"  @: [ "digits"     ::: list ]
>              :| "Fraction" @: [ "pos"        ::: list
>                               , "neg"        ::: list ]
>  , "List"   ::= "Single"   @: [ "single_bit" ::: bit  ]
>              :| "Snoc"     @: [ "snoc_list"  ::: list
>                               , "snoc_bit"   ::: bit  ]
>  , "Bit"    ::= "Zero"     @: []
>              :| "One"      @: []
>  ]
>  where
>   x @: y = x :@ y :& nilT

* Proxies

> pInt    = Proxy :: Proxy Int
> pDouble = Proxy :: Proxy Double

* Attributes

> val   = attr "val"   S pDouble
> len   = attr "len"   S pInt
> scale = attr "scale" I pInt

* Semantic rules

> lenA = syns len
>  [ single |- ⟪ 1 ⟫
>  , snoc   |- ⟪ snoc_list!len + ⟪1⟫ ⟫
>  ]

> valA = syns val
>  [ zero |- ⟪ 0.0 ⟫
>  , one  |- ⟪ ⟪2.0⟫ ** ⟪fromIntegral (par scale)⟫ ⟫
>  ] # collectAlls val sum [integer, fraction, single, snoc]

> scaleA = inhs scale
>  [ digits    |- ⟪ 0 ⟫
>  , pos       |- ⟪ 0 ⟫
>  , neg       |- ⟪ negate (neg!len) ⟫
>  , snoc_list |- ⟪ par scale + ⟪1⟫ ⟫
>  ] # copyN scale [single_bit, snoc_bit]

> allA = valA # lenA # scaleA
 
* Testing
** Building an input tree

> i = node one mempty mempty
> o = node zero mempty mempty
> snocC xs x = node snoc (snoc_list |-> xs \/ snoc_bit |-> x) mempty
> singleC x = node single (single_bit |-> x) mempty
> bits (b:bs) = foldl snocC (singleC b) bs
> as `dot` bs = node fraction (pos |-> bits as \/ neg |-> bits bs) mempty
> int ds = node integer (digits |-> bits ds) mempty

** example input
> ex1 = [i, i, o, i] `dot` [o, i]

** running
> run_val x = case runTree allA number x mempty of
>  Left err -> putStr $ prettyError err
>  Right s -> print (s ! val)
>  where m ! x = fromJust $ lookup_attrs x m
>        fromJust (Just x) = x

* Local variables for emacs

Local Variables:
mode: org
eval: (org-indent-mode -1)
eval: (mmm-ify-by-class 'literate-haskell-bird)
eval: (local-set-key (kbd "<XF86MonBrightnessDown>") 'mmm-parse-buffer)
compile-command: "lhs2TeX --newcode Binary.lhs > Binary.hs && cd ../../..; ghc Grammar/SafeAG/Examples/Binary.hs"
End:
