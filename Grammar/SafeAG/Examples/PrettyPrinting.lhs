%include lhs2TeX.fmt
%include idiom.fmt

\begin{code}
{-# LANGUAGE  QuasiQuotes, TemplateHaskell #-}

module Grammar.SafeAG.Examples.PrettyPrinting where
import Grammar.SafeAG
import Data.Proxy
import Control.Applicative hiding (empty)
import Data.Dynamic
import GHC.Stack
import Grammar.SafeAG.Examples.Idiom

liftA4 f a b c d = liftA3 f a b c <*> d
ifte p t e = if p then t else e

ifteA :: Applicative f => f Bool -> f a -> f a -> f a
ifteA = liftA3 ifte
spaces n = str $ replicate n ' '

pString = Proxy :: Proxy String
pInt = Proxy :: Proxy Int
pBool = Proxy :: Proxy Bool
pList :: Proxy a -> Proxy [a]
pList _ = Proxy
pStrf = Proxy :: Proxy Strf

-- string functions for fast concatenation

type Strf = String -> String
str :: String -> Strf
str = (++)
nil :: Strf
nil = id
append :: Strf -> Strf -> Strf
append = (.)
from_str :: Strf -> String
from_str = ($ "")

-- terminal attributes

string = attr "string" T pString
margin = attr "margin" T pInt

-- grammar

[ pp ::= empty :@ []
     :| text :@ []
     :| indent :@ [indented]
     :| beside :@ [left, right]
     :| above :@ [upper, lower]
 ]
 = grammar $
   [ "PP" ::= "Empty" :@ [] :& x
           :| "Text"  :@ [] :& string & x
           :| "Indent" :@ ["indented" ::: pp] :& margin & x
           :| "Beside" :@ ["left" ::: pp, "right" ::: pp] :& x
           :| "Above" :@ ["upper" ::: pp, "lower" ::: pp] :& x ]
  where x = nilT
        (&) :: Typeable a => Attr T a -> Terminals -> Terminals
        (&) = consT

-- combinators
e   = node empty mempty mempty
t s = node text  mempty (string |=> s)
ind m d = node indent (indented |-> d) (margin |=> m)
l >|< r = node beside (left |-> l \/ right |-> r) mempty
u >-< l = node above (upper |-> u \/ lower |-> l) mempty
a >||< b = a >|< t " " >|< b

{-| example
>>> test example1
when a writer
needs some inspiration there is nothing better
                       |     than
                       |          drinking
-}
example1 = (t "when a writer" >-< t "needs some inspiration ")
  >|< (t "there is nothing better" >-< (t "|" >|< ind 5 (t "than") >-< (t "|" >|< ind 10 (t "drinking"))))

-- attributes

height = attr "height" S pInt
last_width = attr "last_width" S pInt
total_width = attr "total_width" S pInt
body = attr "body" S (pList pStrf)
last_line = attr "last_line" S pStrf

is_empty :: Child -> AR Bool
is_empty c = ⟪ (all (== 0)) ⟪ [c!height, c!total_width, c!last_width] ⟫⟫

emptyA = def_S empty
  [ body        := ⟪ []  ⟫
  , last_line   := ⟪ nil ⟫
  , height      := ⟪ 0   ⟫
  , last_width  := ⟪ 0   ⟫
  , total_width := ⟪ 0   ⟫
  ]

textA = def_S text
  [ body        := ⟪ [] ⟫
  , last_line   := ⟪ str (ter string) ⟫
  , height      := ⟪ 1 ⟫
  , last_width  := len
  , total_width := len]
  where
    len = ⟪ length (ter string) ⟫

indentA = def_S indent
  [ body        --> ⟪ (append <$> tabs) `map` (indented!body) ⟫
  , last_line   --> ⟪ tabs `append` (indented!last_line) ⟫
  , height      :=  indented!height
  , last_width  --> ⟪ ter margin + (indented!last_width) ⟫
  , total_width --> ⟪ ter margin + (indented!total_width) ⟫
  ] where
    infix 0 -->
    x --> y = x := ⟪ if is_empty indented then indented!x else y ⟫
    tabs = ⟪ spaces (ter margin) ⟫

besideA = def_S beside
  [ body        --> ⟪ if ⟪ null (right!body) ⟫ then left!body else beside_body ⟫
  , last_line   --> let before = ⟪ if ⟪ null (right!body) ⟫ then left!last_line else tabs ⟫
                    in ⟪ before `append` (right!last_line) ⟫
  , height      ==> (\l r -> l + r - 1)
  , last_width  ==> (+)
  , total_width --> ⟪ (left!total_width) `max` ⟪left!last_width + right!total_width⟫ ⟫
  ] where
    infix 0 -->, ==>
    x --> y =
      x := ⟪ if is_empty left
             then right!x
             else ⟪ if is_empty right
                    then left!x
                    else y ⟫
           ⟫

    attr ==> op =
      attr --> ⟪ (left!attr) `op` (right!attr) ⟫

    tabs = ⟪ spaces (left!last_width) ⟫

    beside_body = ⟪
      let ts = tabs
          lb = left!body
          ll = left!last_line
          rb : rbs = right!body
      in lb ++ (append ll rb) : (append ts `map` rbs) ⟫

aboveA = def_S above
  [ body        --> ⟪ upper!body ++ ⟪upper!last_line : lower!body⟫ ⟫
  , last_line   ==> lowerP
  , height      ==> (+)
  , last_width  ==> lowerP
  , total_width ==> max
  ] where
    infix 0 -->
    x --> y =
      x := ⟪ if is_empty upper
             then lower!x
             else ⟪ if is_empty lower
                    then upper!x
                    else y ⟫
           ⟫
    attr ==> op =
      attr --> ⟪ (upper!attr) `op` (lower!attr) ⟫
    lowerP u l = l

allA = emptyA # textA # indentA # besideA # aboveA

test x = case runTree allA pp x mempty of
  Left err -> putStr $ prettyError err
  Right s -> do {putStr $ unlines (map from_str (s ! body)); putStrLn (from_str (s ! last_line))}
  where m ! x = fromJust $ lookup_attrs x m
        fromJust (Just x) = x

-- introducing a choice operator and a page width attribute

choice :@ [opt_a, opt_b] =
  productions $
    pp ::= "Choice" :@ ["opt_a" ::: pp, "opt_b" ::: pp] :& nilT

a >^< b = node choice (opt_a |-> a \/ opt_b |-> b) mempty

-- example

pp_ites condD thenD elseD
  =   ifc >||< thent >||< elsee  >||< fi
  >^< ifc >||<  t "then"
      >-< ind 2 thenD
      >-< t "else"
      >-< ind 2 elseD
      >-< fi
  >^< ifc >-< thent >-< elsee  >-< fi
  >^< ifc >||< (thent >-< elsee) >-< fi
  where ifc   = t "if"   >||< condD
        thent = t "then" >||< thenD
        elsee = t "else" >||< elseD
        fi    = t "fi"

example2 = pp_ites (t "x < y") (t "print foobar") (t "print y")

-- page width

pw = attr "page_width" I pInt

{- we will be working on lists of formats now.  Formats are
records of the synthesized attributes height, last_width,
total_width, body, last_line In order to compute the list of
formats we will be using the algebras that are defined by the
previous AG. We need a public access to the AG algebra.

type Algebra = Production :-> SemProd
  = Production :-> ((Child :-> SemTree) -> AttrMap T -> SemTree)
  = Production :-> ((Child :-> (AttrMap I -> AttrMap S)) -> AttrMap T -> AttrMap I -> AttrMap S)
-}

{-
Local Variables:
compile-command: "lhs2TeX --newcode PrettyPrinting.lhs > PrettyPrinting.hs && cd ../../..; ghc Grammar.SafeAG.Examples.PrettyPrinting"
End:
-}
\end{code}
