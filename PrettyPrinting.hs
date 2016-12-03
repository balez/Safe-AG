module PrettyPrinting where
import AG
import Data.Proxy
import Control.Applicative hiding (empty)
import Data.Dynamic

ifte p t e = if p then t else e

pString = Proxy :: Proxy String
pInt = Proxy :: Proxy Int
pBool = Proxy :: Proxy Bool
pList :: Proxy a -> Proxy [a]
pList _ = Proxy
pStrf = Proxy :: Proxy Strf

type Strf = String -> String
str :: String -> Strf
str = (++)
nil :: Strf
nil = id
append :: Strf -> Strf -> Strf
append = (.)

-- terminal attributes

string = attr "string" T pString
margin = attr "margin" T pInt

-- grammar

[ pp ::= empty :@ []
     :| text :@ []
     :| indent :@ [indented]
     :| beside :@ [left, right]
     :| above :@ [upper, lower]
     :| choice :@ [opt_a, opt_b]
 ]
 = grammar $
   [ "PP" ::= "Empty" :@ [] :& x
           :| "Text"  :@ [] :& string & x
           :| "Indent" :@ ["indented" ::: pp] :& margin & x
           :| "Beside" :@ ["left" ::: pp, "right" ::: pp] :& x
           :| "Above" :@ ["upper" ::: pp, "lower" ::: pp] :& x
           :| "Choice" :@ ["opt_a" ::: pp, "opt_b" ::: pp] :& x ]
  where x = nilT
        (&) :: Typeable a => Attr T a -> Terminals -> Terminals
        (&) = consT

-- attributes

height = attr "height" S pInt
last_width = attr "last_width" S pInt
total_width = attr "total_width" S pInt
body = attr "body" S (pList pStrf)
last_line = attr "last_line" S pStrf

emptyA = defS empty
  [ body        |= pure []
  , last_line   |= pure nil
  , height      |= pure 0
  , last_width  |= pure 0
  , total_width |= pure 0]

is_empty c = liftA3 zero (c!height) (c!total_width) (c!last_width)
  where zero 0 0 0 = True
        zero _ _ _ = False

textA = defS text
  [ body |= pure []
  , last_line |= str <$> ter string
  , height     |= pure 1
  , last_width |= len
  , total_width |= len]
  where
    len = length <$> ter string

indentA = defS text
  [ body        --> (\tabs body -> append tabs `map` body) <$> tabs <*> (indented!body)
  , last_line   --> append <$> tabs <*> indented!last_line
  , height      |= indented!height
  , last_width  --> (+) <$> ter margin <*> indented!last_width
  , total_width --> (+) <$> ter margin <*> indented!total_width
  ] where
    infix 0 -->
    x --> y = x |= liftA3 ifte (is_empty indented) (indented!x) y
    tabs = spaces <$> ter margin
    spaces n = str $ replicate n ' '

besideA =
