* Header
Pretty printing library following the apparoach of
"Optimal Pretty-Printing Combinators" by Pablo R. Azero and S. Doaitse Swierstra
and "Designing and Implementing Combinator Languages"
by S. Doaitse Swierstra1 , Pablo R. Azero Alcocer1 , and Joao Saraiva

** Lhs2TeX
%include lhs2TeX.fmt
%include applicative.fmt
** GHC Extensions

> {-# LANGUAGE TemplateHaskell #-}

** Module Exports

> module Grammar.SafeAG.Examples.PrettyPrinting where

** Module Imports

> import Grammar.SafeAG
> import Data.Proxy
> import Control.Applicative hiding (empty)
> import Data.Dynamic (Typeable)
> import Grammar.SafeAG.TH.Idiom
> import Grammar.SafeAG.TH.Applicative

* Type proxies

> pString = Proxy :: Proxy String
> pInt    = Proxy :: Proxy Int
> pBool   = Proxy :: Proxy Bool
> pStrf   = Proxy :: Proxy Strf
> pList :: Proxy a -> Proxy [a]
> pList _ = Proxy

* String functions for fast concatenation

> type Strf = String -> String
> str      :: String -> Strf
> nil      :: Strf
> (++.) :: Strf -> Strf -> Strf
> from_str :: Strf -> String

> str      = (++)
> nil      = id
> (++.)    = (.)
> from_str = ($ "")
> spaces n = str $ replicate n ' '

* Terminal attributes

> string = attr "string" T pString
> margin = attr "margin" T pInt

* Grammar

 > [ pp ::= empty :@ []
 >      :| text :@ []
 >      :| indent :@ [indented]
 >      :| beside :@ [left, right]
 >      :| above :@ [upper, lower]
 >  ]
 >  = grammar $
 >    [ "PP" ::= "Empty" :@ [] :& x
 >            :| "Text"  :@ [] :& string & x
 >            :| "Indent" :@ ["indented" ::: pp] :& margin & x
 >            :| "Beside" :@ ["left" ::: pp, "right" ::: pp] :& x
 >            :| "Above" :@ ["upper" ::: pp, "lower" ::: pp] :& x ]
 >   where x = nilT
 >         (&) :: Typeable a => Attr T a -> Terminals -> Terminals
 >         (&) = consT



 > [ pp ::= empty :@ []
 >      :| text :@ []
 >      :| indent :@ [indented]
 >      :| beside :@ [left, right]
 >      :| above :@ [upper, lower]
 >  ]
 >  = grammar $
 >    [ "PP" ::= "Empty" :@ [] :& ()
 >            :| "Text"  :@ [] :& string
 >            :| "Indent" :@ ["indented" ::: pp] :& margin
 >            :| "Beside" :@ ["left" ::: pp, "right" ::: pp] :& ()
 >            :| "Above" :@ ["upper" ::: pp, "lower" ::: pp] :& () ]

 > pp = non_terminal "PP"
 > empty = production pp "Empty" [] ()
 > text = production pp "Text" [] string
 > indent = production pp "Indent" [indented] margin
 > beside = production pp "Beside" [left, right] ()
 > above = production pp "Above" [upper, lower] ()
 > indented = child indent "indented" pp
 > left = child beside "left" pp
 > right = child beside "right" pp
 > upper = child above "upper" pp
 > lower = child above "lower" pp

> pp = non_terminal "PP"
> empty :@ [] = prod pp "Empty" [] ()
> text :@ [] = prod pp "Text" [] string
> indent :@ [indented] =
>   prod pp "Indent" ["indented" ::: pp] margin
> beside :@ [left, right] =
>   prod pp "Beside" ["left" ::: pp, "right" ::: pp] ()
> above :@ [upper, lower] =
>   prod pp "Above" ["upper" ::: pp, "lower" ::: pp] ()


* Combinators (smart constructors)

> e   = node empty mempty mempty
> t s = node text  mempty (string |=> s)
> ind m d = node indent (indented |-> d) (margin |=> m)
> l >|< r = node beside (left |-> l \/ right |-> r) mempty
> u >-< l = node above (upper |-> u \/ lower |-> l) mempty
> a >||< b = a >|< t " " >|< b

** Example
 >>> test example1
 when a writer
 needs some inspiration there is nothing better
                        |     than
                        |          drinking

> example1 = (t "when a writer" >-< t "needs some inspiration ")
>   >|< (t "there is nothing better" >-< (t "|" >|< ind 5 (t "than") >-< (t "|" >|< ind 10 (t "drinking"))))
>

* Attributes

> height = attr "height" S pInt
> last_width = attr "last_width" S pInt
> total_width = attr "total_width" S pInt
> body = attr "body" S (pList pStrf)
> last_line = attr "last_line" S pStrf

* Rules

> is_empty :: Child -> AR Bool
> is_empty c = ⟦ all (== 0) [⟨c!height⟩, ⟨c!total_width⟩, ⟨c!last_width⟩] ⟧

> emptyA = def_S empty
>   [ body        := ⟦ []  ⟧
>   , last_line   := ⟦ nil ⟧
>   , height      := ⟦ 0   ⟧
>   , last_width  := ⟦ 0   ⟧
>   , total_width := ⟦ 0   ⟧
>   ]

> textA = def_S text
>   [ body        := ⟦ [] ⟧
>   , last_line   := ⟦ str ⟨ter string⟩ ⟧
>   , height      := ⟦ 1 ⟧
>   , last_width  := len
>   , total_width := len
>   ]
>   where
>     len = ⟦ length ⟨ter string⟩ ⟧

> indentA = def_S indent
>   [ body        --> ⟦ (⟨tabs⟩ ++.) `map` ⟨indented!body⟩ ⟧
>   , last_line   --> ⟦ ⟨tabs⟩ ++. ⟨indented!last_line⟩ ⟧
>   , height      :=  indented!height
>   , last_width  --> ⟦ ⟨ter margin⟩ + ⟨indented!last_width⟩ ⟧
>   , total_width --> ⟦ ⟨ter margin⟩ + ⟨indented!total_width⟩ ⟧
>   ] where
>     infix 0 -->
>     x --> y = x := ⟦ if ⟨is_empty indented⟩ then ⟨indented!x⟩ else ⟨y⟩ ⟧
>     tabs = ⟦ spaces ⟨ter margin⟩ ⟧

> besideA = def_S beside
>   [ body        --> ⟦
>       case ⟨right!body⟩ of
>         [] -> ⟨left!body⟩
>         rb : rbs -> ⟨left!body⟩ ++ (⟨left!last_line⟩ ++. rb)
>                     : (⟨tabs⟩ ++.) `map` rbs
>       ⟧
>   , last_line   --> ⟦ let before = if null ⟨right!body⟩ then ⟨left!last_line⟩ else ⟨tabs⟩
>                       in before ++. ⟨right!last_line⟩ ⟧
>   , height      ==> (\l r -> l + r - 1)
>   , last_width  ==> (+)
>   , total_width --> ⟦ ⟨left!total_width⟩ `max` ⟨left!last_width⟩ + ⟨right!total_width⟩ ⟧
>   ] where
>     infix 0 -->, ==>
>     x --> y =
>       x := ⟦ if ⟨is_empty left⟩
>              then ⟨right!x⟩
>              else if ⟨is_empty right⟩
>                   then ⟨left!x⟩
>                   else ⟨y⟩
>            ⟧
>
>     attr ==> op =
>       attr --> ⟦ ⟨left!attr⟩ `op` ⟨right!attr⟩ ⟧
>
>     tabs = ⟦ spaces ⟨left!last_width⟩ ⟧

> aboveA = def_S above
>   [ body        --> ⟦ ⟨upper!body⟩ ++ ⟨upper!last_line⟩ : ⟨lower!body⟩ ⟧
>   , last_line   ==> lowerP
>   , height      ==> (+)
>   , last_width  ==> lowerP
>   , total_width ==> max
>   ] where
>     infix 0 -->
>     x --> y =
>       x := ⟦ if ⟨is_empty upper⟩
>              then ⟨lower!x⟩
>              else if ⟨is_empty lower⟩
>                   then ⟨upper!x⟩
>                   else ⟨y⟩
>            ⟧
>     attr ==> op =
>       attr --> ⟦ ⟨upper!attr⟩ `op` ⟨lower!attr⟩ ⟧
>     lowerP u l = l

> allA = emptyA # textA # indentA # besideA # aboveA

** Tests

> test x = case runTree allA pp x mempty of
>   Left err -> putStr $ prettyError err
>   Right s -> do {putStr $ unlines (map from_str (s ! body)); putStrLn (from_str (s ! last_line))}
>   where m ! x = fromJust $ lookup_attrs x m
>         fromJust (Just x) = x

* Local variables for emacs
Local Variables:
mode: org
eval: (org-indent-mode -1)
eval: (mmm-mode)
eval: (mmm-ify-by-class 'literate-haskell-bird)
eval: (local-set-key (kbd "<XF86MonBrightnessDown>") 'mmm-parse-buffer)
compile-command: "lhs2TeX --newcode PrettyPrinting.lhs > PrettyPrinting.hs && cd ../../..; ghc Grammar.SafeAG.Examples.PrettyPrinting"
End:
