* Overview
Extension to the pretty printing library.

* Header
** Lhs2TeX
%include lhs2TeX.fmt
%include applicative.fmt
** GHC Extensions

> {-# LANGUAGE TemplateHaskell, RecordWildCards, RankNTypes, NoMonomorphismRestriction #-}

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
Introducing a choice operator and a page width attribute.

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
algebras of the AG defined in PrettyPrinting.lhs

** Format

> data Format = Format
>  { body         :: [Strf]
>  , last_line    :: Strf
>  , height       :: Int
>  , last_width   :: Int
>  , total_width  :: Int
>  }

*** instances Eq, Ord

Eq and Ord instances ignore the textual content of the format.

> instance Eq Format  where
>   x == y = height   x == height y
>          && total_width x == total_width y
>          && last_width  x == last_width y

> instance Ord Format where
>   x <= y = x == y || x < y
>   x < y = height x < height y
>         || ( height x == height y
>         && total_width x < total_width y )

*** is_empty

> is_empty (Format{..}) =
>  all (== 0) [height, total_width, last_width]

*** fmts: Lists of Formats
**** Proxy
> pFormat :: Proxy Format
> pFormat = Proxy
**** Attribute

> fmts = attr "fmts" S (pList pFormat)

**** AG-Algebra for Format
***** Conversions from format to attributes
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
> fmtAlg terminals input =
>   ⟦ \env terms -> ⟨algAR mempty terminals fmtDesc PP.allA input⟩ terms env () ⟧

***** Algebras
****** Builder
> data AlgBuildS s = AlgBuildS
>  { alg0  :: Production -> AR s
>  , alg0T :: forall t . Typeable t => Production -> Attr T t -> AR (t -> s)
>  , alg1T :: forall t . Typeable t => Child -> Attr T t -> AR (t -> s -> s)
>  , alg2  :: Child -> Child -> AR (s -> s -> s)
>  , algN  :: Production -> AR ([s] -> s)
>  }

> algBuildS :: SynDesc s -> (Child -> AlgInput s) -> Aspect -> AlgBuildS s
> algBuildS sdesc input aspect =
>   let alg inp = ⟦ \e -> ⟨algAR mempty mempty sdesc aspect inp⟩ () e () ⟧
>       algT tdesc inp = ⟦ \t e -> ⟨algAR mempty tdesc sdesc aspect inp⟩ t e () ⟧
>       zip = zipInput `on` input
>       inputs p = foldr inputs_cons (emptyInput p) (prod_children p)
>       inputs_cons c is = (\(h:t) -> (h,t)) `map_env` zipInput (input c) is
>   in AlgBuildS
>   { alg0 = \p -> ⟦ ⟨alg (emptyInput p)⟩ () ⟧
>   , alg0T = \p a -> ⟦ \t -> ⟨algT (embed a id) (emptyInput p)⟩ t () ⟧
>   , alg1T = \c a -> algT (embed a id) (input c)
>   , alg2 = \x y -> ⟦ curry ⟨alg (x `zip` y)⟩ ⟧
>   , algN = alg . inputs
>   }


****** PP algebra builder

> empty_alg  (AlgBuildS{..}) = alg0  empty
> text_alg   (AlgBuildS{..}) = alg0T text string
> indent_alg (AlgBuildS{..}) = alg1T indented margin
> beside_alg (AlgBuildS{..}) = alg2  left right
> above_alg  (AlgBuildS{..}) = alg2  upper lower
> choice_alg (AlgBuildS{..}) = alg2  opt_a opt_b

****** Format algebras

> fmtBuild = algBuildS fmtDesc fmtInput PP.allA

> empty_fmt  = empty_alg  fmtBuild
> text_fmt   = text_alg   fmtBuild
> indent_fmt = indent_alg fmtBuild
> beside_fmt = beside_alg fmtBuild
> above_fmt  = above_alg  fmtBuild
> choice_fmt = choice_alg fmtBuild

< data PPAlg a = PPAlg
< { empty_alg  :: a
< , text_alg   :: String -> a
< , indent_alg :: Int -> a -> a
< , beside_alg :: a -> a -> a
< , above_alg  :: a -> a -> a
< , choice_alg :: a -> a -> a
< }

**** Rules

> fmtsA = syns fmts
>   [ empty  |- ⟦ [ ⟨empty_fmt⟩ ] ⟧
>   , text   |- ⟦ let s = ⟨ter string⟩
>                 in if (length s <= ⟨par pw⟩) then [ ⟨text_fmt⟩ s ] else [] ⟧
>   , indent |- ⟦ dropWhile ((> ⟨par pw⟩) . total_width)
>                           (⟨indent_fmt⟩ ⟨ter margin⟩ `map` ⟨indented!fmts⟩) ⟧
>   , above  |- ⟦ sort [ ⟨above_fmt⟩ u l | u <- ⟨upper!fmts⟩, l <- ⟨lower!fmts⟩ ] ⟧
>   , beside |- ⟦ sort . concat $ ⟨beside_candidates⟩ ⟧
>   ]

> beside_candidates =
>   ⟦ [ map (⟨beside_fmt⟩ l) . dropWhile (tooWide ⟨par pw⟩ l) $ ⟨right!fmts⟩ | l <- ⟨left!fmts⟩ ] ⟧

> tooWide pw x y = new_w > pw
>  where new_w = total_width x `max` (last_width x + total_width y)


Optimized versions

TODO: share empty and text with fmtsA

> fmtsOptimA = syns fmts
>   [ empty  |- ⟦ [ ⟨empty_fmt⟩ ] ⟧
>   , text   |- ⟦ let s = ⟨ter string⟩
>                 in if (length s <= ⟨par pw⟩) then [ ⟨text_fmt⟩ s ] else [] ⟧
>   , indent |- ⟦ let { m = ⟨ter margin⟩
>                     ; dont_fit fmt = total_width fmt > ⟨par pw⟩ - m }
>                 in ⟨indent_fmt⟩ m `map` dropWhile dont_fit ⟨indented!fmts⟩ ⟧
>   , above  |- ⟦ mergel [map (⟨above_fmt⟩ u) ⟨lower!fmts⟩ | u <- ⟨upper!fmts⟩ ] ⟧
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

** Splitting Combinators

< hor_or_ver pw es
<   = choice_fmts pw ver_fmts
<                    (if allh1 then hor_fmts
<                              else fail_fmts)
<  where
<    e_fmts   = map (doc2fmts pw) es
<    hor_fmts = foldr1 (beside_fmts pw) e_fmts
<    ver_fmts = foldr1 (above_fmts pw) e_fmts
<    allh1 = and
<          . map ((== 1) . height . head)
<          $ e_fmts
<    fail_fmts = []

> hor_or_ver :@ [docs] =
>   productions $
>     pp ::= "Hor_or_ver" :@ ["docs" ::: list_pp] :& nilT

> [ list_pp ::= cons_pp :@ [head_pp, tail_pp]
>           :|  nil_pp :@ []
>  ] = grammar $
>  [ "List_PP" ::= "Cons_PP" :@ [ "head_pp" ::: pp
>                               , "tail_pp" ::: list_pp] :& nilT
>              :|  "Nil_PP" :@ [] :& nilT ]

*** AG-Alg for fmts
In the article implementation, `hor_or_ver' is defined in terms
of the format lists primitives. Since we defined them as
attributes, we must compute the AG-algebras.

*** Algebra Builder with inherited attributes

> data AlgBuildI i s = AlgBuildI
>  { algi0  :: Production -> AR (i -> s)
>  , algi0T :: forall t . Typeable t => Production -> Attr T t -> AR (i -> t -> s)
>  , algi1T :: forall t . Typeable t => Child -> Attr T t -> AR (i -> t -> s -> s)
>  , algi2  :: Child -> Child -> AR (i -> s -> s -> s)
>  , algiN  :: Production -> AR (i -> [s] -> s)
>  }

> algBuildI :: InhDesc i -> SynDesc s -> (Child -> AlgInput s) -> Aspect -> AlgBuildI i s
> algBuildI idesc sdesc input aspect =
>   let alg inp = ⟦ \i e -> ⟨algAR idesc mempty sdesc aspect inp⟩ () e i ⟧
>       algT tdesc inp = ⟦ \i t e -> ⟨algAR idesc tdesc sdesc aspect inp⟩ t e i ⟧
>       zip = zipInput `on` input
>       inputs p = foldr inputs_cons (emptyInput p) (prod_children p)
>       inputs_cons c is = (\(h:t) -> (h,t)) `map_env` zipInput (input c) is
>   in AlgBuildI
>   { algi0 = \p -> ⟦ \i -> ⟨alg (emptyInput p)⟩ i () ⟧
>   , algi0T = \p a -> ⟦ \i t -> ⟨algT (embed a id) (emptyInput p)⟩ i t () ⟧
>   , algi1T = \c a -> algT (embed a id) (input c)
>   , algi2 = \x y -> ⟦ \i -> curry (⟨alg (x `zip` y)⟩ i) ⟧
>   , algiN = alg . inputs
>   }

*** PP algebra builder

> empty_algi  (AlgBuildI{..}) = algi0  empty
> text_algi   (AlgBuildI{..}) = algi0T text string
> indent_algi (AlgBuildI{..}) = algi1T indented margin
> beside_algi (AlgBuildI{..}) = algi2  left right
> above_algi  (AlgBuildI{..}) = algi2  upper lower
> choice_algi (AlgBuildI{..}) = algi2  opt_a opt_b

*** Fmts algebras

> fmtsInput child = synAlgs child [ fmts := askE ]
> fmtsBuild = algBuildI (embed pw id) (project fmts) fmtsInput fmtsOptimA

> empty_fmts  = empty_algi  fmtsBuild
> text_fmts   = text_algi   fmtsBuild
> indent_fmts = indent_algi fmtsBuild
> beside_fmts = beside_algi fmtsBuild
> above_fmts  = above_algi  fmtsBuild
> choice_fmts = choice_algi fmtsBuild

*** Rules

> fmtss = attr "fmtss" S (pList (pList pFormat))

Thanks to the effectful notation, we are able to write almost the same
definition as in the article.

> hor_or_verA = syns fmts
>  [ hor_or_ver |- ⟦ case()of{_->
>      ⟨choice_fmts⟩ pw' ver_fmts
>                       (if allh1 then hor_fmts
>                                 else fail_fmts)
>       where
>         pw' = ⟨par pw⟩
>         e_fmts   = ⟨docs!fmtss⟩
>         hor_fmts = foldr1 (⟨beside_fmts⟩ pw') e_fmts
>         ver_fmts = foldr1 (⟨above_fmts⟩ pw') e_fmts
>         allh1 = and
>               . map ((== 1) . height . head)
>               $ e_fmts
>         fail_fmts = []
>    }⟧
>  ] # syns fmtss
>  [ nil_pp |- ⟦ [] ⟧
>  , cons_pp |- ⟦ ⟨head_pp!fmts⟩ : ⟨tail_pp!fmtss⟩ ⟧
>  ]

* Local variables for emacs
Local Variables:
mode: org
eval: (org-indent-mode -1)
eval: (mmm-mode)
eval: (mmm-ify-by-class 'literate-haskell-bird)
eval: (local-set-key (kbd "<XF86MonBrightnessDown>") 'mmm-parse-buffer)
compile-command: "lhs2TeX --newcode PrettyPrintingExt.lhs > PrettyPrintingExt.hs && cd ../../..; ghc Grammar.SafeAG.Examples.PrettyPrintingExt"
End:
