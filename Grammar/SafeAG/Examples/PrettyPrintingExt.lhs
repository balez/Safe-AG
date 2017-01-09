* Overview
Extension to the pretty printing library.

* Header
** Lhs2TeX
%include lhs2TeX.fmt
%include applicative.fmt
** GHC Extensions

> {-# LANGUAGE TemplateHaskell, RecordWildCards #-}

** Module Exports

> module Grammar.SafeAG.Examples.PrettyPrintingExt where

** Module Imports

> import Grammar.SafeAG
> import qualified Grammar.SafeAG.Examples.PrettyPrinting as PP
> import Grammar.SafeAG.Examples.PrettyPrinting hiding (height, last_width, total_width, body, last_line, is_empty)
> import Data.Proxy
> import Data.List (sort)
> import Data.Function (on)
> import Control.Applicative hiding (empty)
> import Data.Dynamic (Typeable)
> import Grammar.SafeAG.TH.Idiom
> import Grammar.SafeAG.TH.Applicative

* Extensions
** Choice
Introducing a choice operator and a page width attribute

> choice :@ [opt_a, opt_b] =
>   productions $
>     pp ::= "Choice" :@ ["opt_a" ::: pp, "opt_b" ::: pp] :& nilT
>
> a >^< b = node choice (opt_a |-> a \/ opt_b |-> b) mempty

*** Example

> pp_ites condD thenD elseD
>   =   ifc >||< thent >||< elsee  >||< fi
>   >^< ifc >||<  t "then"
>       >-< ind 2 thenD
>       >-< t "else"
>       >-< ind 2 elseD
>       >-< fi
>   >^< ifc >-< thent >-< elsee  >-< fi
>   >^< ifc >||< (thent >-< elsee) >-< fi
>   where ifc   = t "if"   >||< condD
>         thent = t "then" >||< thenD
>         elsee = t "else" >||< elseD
>         fi    = t "fi"

> example2 = pp_ites (t "x < y") (t "print foobar") (t "print y")

** Page width

> pw = attr "page_width" I pInt

We will be working on lists of formats now.  Formats are
records of the synthesized attributes height, last_width,
total_width, body, last_line.

In order to compute the list of formats we will be using the
algebras that are defined by the previous AG.

** Format

> data Format = Format
>  { body         :: [Strf]
>  , last_line    :: Strf
>  , height       :: Int
>  , last_width   :: Int
>  , total_width  :: Int
>  }

-- Eq and Ord instances ignore the textual content of the format.

> instance Eq Format  where
>   x == y = height   x == height y
>          && total_width x == total_width y
>          && last_width  x == last_width y

> instance Ord Format where
>   x <= y = x == y || x < y
>   x < y = height x < height y
>         || ( height x == height y
>         && total_width x < total_width y )

> is_empty (Format{..}) =
>  all (== 0) [height, total_width, last_width]

> pFormat :: Proxy Format
> pFormat = Proxy

> fmts = attr "fmts" S (pList pFormat)

** Rules

> fmtDesc = ⟦
>   Format
>   { body        = ⟨project PP.body⟩
>   , last_line   = ⟨project PP.last_line⟩
>   , height      = ⟨project PP.height⟩
>   , last_width  = ⟨project PP.last_width⟩
>   , total_width = ⟨project PP.total_width⟩
>   } ⟧

> fmtDefs =
>   [ PP.body        := projE body
>   , PP.last_line   := projE last_line
>   , PP.height      := projE height
>   , PP.last_width  := projE last_width
>   , PP.total_width := projE total_width ]

> fmtInput child = synAlgs child fmtDefs
> fmtAlg terminals aspect input =
>   ⟦ \env terms -> ⟨algAR mempty terminals fmtDesc aspect input⟩ env terms () ⟧

> emptyFmt  = ⟦ ⟨fmtAlg mempty PP.emptyA (emptyInput empty)⟩ () () ⟧
> textFmt   = ⟦ \s -> ⟨fmtAlg (embed string id) PP.textA (emptyInput text)⟩ () s ⟧
> indentFmt = ⟦ \m d -> ⟨fmtAlg (embed margin id) PP.indentA (fmtInput indented)⟩ d m ⟧
> besideFmt = ⟦ \l r -> ⟨fmtAlg mempty PP.besideA (left `zipFmtInput` right)⟩ (l, r) () ⟧
> aboveFmt  = ⟦ \u l -> ⟨fmtAlg mempty PP.aboveA (upper `zipFmtInput` lower)⟩ (u, l) () ⟧

> zipFmtInput = zipInput `on` fmtInput

> fmtsA = syns fmts
>   [ empty  |- ⟦ [ ⟨emptyFmt⟩ ] ⟧
>   , text   |- ⟦ let s = ⟨ter string⟩
>                 in if (length s <= ⟨par pw⟩) then [ ⟨textFmt⟩ s ] else [] ⟧
>   , indent |- ⟦ dropWhile ((> ⟨par pw⟩) . total_width)
>                           (⟨indentFmt⟩ ⟨ter margin⟩ `map` ⟨indented!fmts⟩) ⟧
>   , above  |- ⟦ sort [ ⟨aboveFmt⟩ u l | u <- ⟨upper!fmts⟩, l <- ⟨lower!fmts⟩ ] ⟧
>   , beside |- ⟦ sort . concat $ ⟨beside_candidates⟩ ⟧
>   ]

> beside_candidates =
>   ⟦ [ map (⟨besideFmt⟩ l) . dropWhile (tooWide ⟨par pw⟩ l) $ ⟨right!fmts⟩ | l <- ⟨left!fmts⟩ ] ⟧

> tooWide pw x y = new_w > pw
>  where new_w = total_width x `max` (last_width x + total_width y)


Optimized versions

> fmtsOptimA = syns fmts
>   [ indent |- ⟦ let { m = ⟨ter margin⟩
>                     ; dont_fit fmt = total_width fmt > ⟨par pw⟩ - m }
>                 in ⟨indentFmt⟩ m `map` dropWhile dont_fit ⟨indented!fmts⟩ ⟧
>   , above  |- ⟦ mergel [map (⟨aboveFmt⟩ u) ⟨lower!fmts⟩ | u <- ⟨upper!fmts⟩ ] ⟧
>   , beside |- ⟦ mergel ⟨beside_candidates⟩ ⟧
>   , choice |- ⟦ merge ⟨opt_a!fmts⟩ ⟨opt_b!fmts⟩ ⟧ -- i'm not sure if that's what was meant in the article
>   ]

> mergel :: Ord a => [[a]] -> [a]
> mergel = foldr merge []

> merge l@(x:xs) r@(y:ys)
>   | x <= y = x : merge xs r
>   | otherwise = y : merge l ys
> merge [] r = r
> merge l [] = l

* Splitting Combinators

< hor_or_ver pw es
<   = choice_fmts pw ver_fmts
<                    (if allh1 then hor_fmts
<                              else fail_fmts)
<  where
<    e_fmts   = map (doc2fmts pw) es
<    hor_fmts = foldr1 (beside_fmts pw) e_fmts
<    ver_fmts = foldr1 (above_fmts pw) e_fmts
<    allh1 = and
<          . map ((==1).height . head)
<          $ e_fmts
< fail_fmts = []

* Local variables for emacs
Local Variables:
mode: org
eval: (org-indent-mode -1)
eval: (mmm-mode)
eval: (mmm-ify-by-class 'literate-haskell-bird)
eval: (local-set-key (kbd "<XF86MonBrightnessDown>") 'mmm-parse-buffer)
compile-command: "lhs2TeX --newcode PrettyPrintingExt.lhs > PrettyPrintingExt.hs && cd ../../..; ghc Grammar.SafeAG.Examples.PrettyPrintingExt"
End:
