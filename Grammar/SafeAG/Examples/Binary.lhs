The attribute grammar for binary number is the example given
in Knuth original paper "Semantics of Context Free Languages".

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

> module Grammar.SafeAG.Examples.Binary where
> import Data.Proxy (Proxy(..))
> import Data.Ratio
> import Control.Applicative
> import Grammar.SafeAG
> import Grammar.SafeAG.TH.Applicative

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

> number = non_terminal "number"
> list = non_terminal "list"
> bit = non_terminal "bit"
 
 > integer :@ [digits] = prod number
 >   "integer" ["digits" ::: list] ()
 > fraction :@ [pos, neg] = prod number
 >   "fraction" ["pos" ::: list, "neg" ::: list] ()
 > single :@ [single_bit] = prod list
 >   "single" ["single_bit" ::: bit] ()
 > snoc :@ [snoc_list, snoc_bit] = prod list
 >   "snoc" ["snoc_list" ::: list, "snoc_bit" ::: bit] ()
 > zero :@ [] = prod bit "zero" [] ()
 > one :@ [] = prod bit "one" [] ()

> integer = production number "integer" [digits] ()
> fraction = production number "fraction" [pos, neg] ()
> single = production list "single" [single_bit] ()
> snoc = production list "snoc" [snoc_list, snoc_bit] ()
> zero = production bit "zero" [] ()
> one = production bit "one" [] ()

> digits = child integer "digits" list
> pos = child fraction "pos" list
> neg = child fraction "neg" list
> single_bit = child single "single_bit" bit
> snoc_list = child snoc "snoc_list" list
> snoc_bit = child snoc "snoc_bit" bit

* Proxies

> pInt    = Proxy :: Proxy Int
> pDouble = Proxy :: Proxy Double

* Attributes

> val   = attr "val"   S pDouble
> len   = attr "len"   S pInt
> scale = attr "scale" I pInt

* Semantic rules

> lenA = syns len
>  [ single |- ⟦ 1 ⟧
>  , snoc   |- ⟦ ⟨snoc_list!len⟩ + 1 ⟧
>  ]

> valA = syns val
>  [ zero |- ⟦ 0.0 ⟧
>  , one  |- ⟦ 2.0 ** fromIntegral ⟨par scale⟩ ⟧
>  ] # collectAlls val sum [integer, fraction, single, snoc]

> scaleA = inhs scale
>  [ digits    |- ⟦ 0 ⟧
>  , pos       |- ⟦ 0 ⟧
>  , neg       |- ⟦ negate ⟨neg!len⟩ ⟧
>  , snoc_list |- ⟦ ⟨par scale⟩ + 1 ⟧
>  ] # copyN scale [single_bit, snoc_bit]

> allA = valA # lenA # scaleA
 
* Testing
** Building an input tree

> i = node one mempty mempty
> o = node zero mempty mempty
> snocC xs x = node snoc (snoc_list |-> xs \/ snoc_bit |-> x) mempty
> singleC x = node single (single_bit |-> x) mempty
> bits (b:bs) = foldl snocC (singleC b) bs
> bits [] = singleC o
> as `dot` bs = node fraction (pos |-> bits as \/ neg |-> bits bs) mempty
> int ds = node integer (digits |-> bits ds) mempty


** example input

> ex1 = [i,i,o,i] `dot` [o,i] -- 13.25
> ex2 = [i,o,o,o,o,o,i,i,i,o] `dot` [i,o,i] -- 526.625

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
