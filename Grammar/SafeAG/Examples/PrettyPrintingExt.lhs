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
> import Grammar.SafeAG.Examples.PrettyPrinting
>   hiding (height, last_width, total_width, body, last_line, is_empty)
> import Data.Proxy
> import Data.List (sort)
> import Data.Function (on)
> import Control.Applicative hiding (empty)
> import Data.Dynamic (Typeable)
> import Grammar.SafeAG.TH.Idiom
> import Grammar.SafeAG.TH.Applicative

* Algebra builder

Using `algAR' can be a bit verbose. We define a helper that
specialises `algAR' to productions of different arities:
different number of terminals and children.  Note that this
helper is specific to a case when all the children have the
same attributes, but this is the most common case.

> data AlgBuilder i s = AlgBuilder
>  { alg0  :: Production -> AR (i -> s)
>  , alg0T :: forall a . Typeable a => Production -> Attr T a -> AR (i -> a -> s)
>  , alg0T2 :: forall a b . (Typeable a, Typeable b) => Production -> Attr T a -> Attr T b -> AR (i -> a -> b -> s)
>  , alg1 :: Child -> AR (i -> s -> s)
>  , alg1T :: forall a . Typeable a => Child -> Attr T a -> AR (i -> a -> s -> s)
>  , alg1T2 :: forall a b . (Typeable a, Typeable b) => Child -> Attr T a -> Attr T b -> AR (i -> a -> b -> s -> s)
>  , alg2  :: Child -> Child -> AR (i -> s -> s -> s)
>  , alg2T :: forall a . Typeable a => Child -> Child -> Attr T a -> AR (i -> a -> s -> s -> s)
>  , alg2T2 :: forall a b . (Typeable a, Typeable b) => Child -> Child -> Attr T a -> Attr T b -> AR (i -> a -> b -> s -> s -> s)
>  , algN  :: Production -> AR (i -> [s] -> s)
>  }

> algBuilder :: InhDesc i -> SynDesc s -> (Child -> AlgInput s) -> Aspect -> AlgBuilder i s
> algBuilder idesc sdesc input aspect =
>   let alg inp = ⟦ \i -> ⟨algAR aspect idesc (inDesc []) inp sdesc⟩ i () ⟧
>       algT tdesc inp = algAR aspect idesc tdesc inp sdesc
>       zip = zipInput `on` input
>       inputs p = foldr inputs_cons (emptyInput p) (prod_children p)
>       inputs_cons c is = (\(h:t) -> (h,t)) `map_env` zipInput (input c) is
>   in AlgBuilder
>   { alg0 = \p -> ⟦ \i -> ⟨alg (emptyInput p)⟩ i () ⟧
>   , alg0T = \p a -> ⟦ \i t -> ⟨algT (inDesc [a <-- id]) (emptyInput p)⟩ i t () ⟧
>   , alg0T2 = \p a b -> ⟦ \i a' b' -> ⟨algT (inDesc [a <-- fst, b <-- snd]) (emptyInput p)⟩ i (a',b') () ⟧
>   , alg1  = \x -> alg (input x)
>   , alg1T = \x a -> algT (inDesc [a <-- id]) (input x)
>   , alg1T2 = \x a b -> ⟦ \i a' b' x' -> ⟨algT (inDesc [a <-- fst, b <-- snd]) (input x)⟩ i (a',b') x'⟧
>   , alg2 = \x y -> ⟦ \i x' y' -> ⟨alg (x `zip` y)⟩ i (x', y') ⟧
>   , alg2T = \x y a -> ⟦ \i a' x' y' -> ⟨algT (inDesc [a <-- id]) (x `zip` y)⟩ i a' (x',y') ⟧
>   , alg2T2 = \x y a b -> ⟦ \i a' b' x' y' -> ⟨algT (inDesc [a <-- fst, b <-- snd]) (x `zip` y)⟩ i (a', b') (x', y') ⟧
>   , algN = alg . inputs
>   }

** PP algebras

> empty_alg  (AlgBuilder{..}) = alg0  empty
> text_alg   (AlgBuilder{..}) = alg0T text string
> indent_alg (AlgBuilder{..}) = alg1T indented margin
> beside_alg (AlgBuilder{..}) = alg2  left right
> above_alg  (AlgBuilder{..}) = alg2  upper lower
> choice_alg (AlgBuilder{..}) = alg2  opt_a opt_b

* Extensions
** Choice
Introducing a choice operator and a page width attribute.

> choice :@ [opt_a, opt_b] = prodnchild pp
>     "Choice" ["opt_a" ::: pp, "opt_b" ::: pp] ()

> a >^< b = node choice (opt_a |-> a \/ opt_b |-> b) mempty

*** Deprecated syntax
 > choice :@ [opt_a, opt_b] =
 >   productions $
 >     pp ::= "Choice" :@ ["opt_a" ::: pp, "opt_b" ::: pp] :& nilT


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

> pw = attr I "page_width" pInt

`pw' is copied everywhere. I think it is good that we are
required to name explicitely the children where an attribute
is copied.

> pwA = copyPs pw [indent, beside, above, choice]
>       # copyN pw [docs, head_pp, tail_pp]

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

> fmts = attr S "fmts" (pList pFormat)

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

> fmtInput = algInput
>   [ PP.body        := projE body
>   , PP.last_line   := projE last_line
>   , PP.height      := projE height
>   , PP.last_width  := projE last_width
>   , PP.total_width := projE total_width ]

***** Algebras
****** Format algebras

> fmtBuild = algBuilder (inDesc []) fmtDesc fmtInput PP.allA

> empty_fmt  = ⟦ ⟨empty_alg  fmtBuild⟩ () ⟧
> text_fmt   = ⟦ ⟨text_alg   fmtBuild⟩ () ⟧
> indent_fmt = ⟦ ⟨indent_alg fmtBuild⟩ () ⟧
> beside_fmt = ⟦ ⟨beside_alg fmtBuild⟩ () ⟧
> above_fmt  = ⟦ ⟨above_alg  fmtBuild⟩ () ⟧
> choice_fmt = ⟦ ⟨choice_alg fmtBuild⟩ () ⟧

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
*** Grammar extension
> hor_or_ver :@ [docs] = prodnchild pp
>  "Hor_or_ver" ["docs" ::: list_pp] ()

> list_pp = non_terminal "List_PP"
> cons_pp :@ [head_pp, tail_pp] = prodnchild list_pp
>   "Cons_PP" [ "head_pp" ::: pp, "tail_pp" ::: list_pp] ()

> nil_pp :@ [] = prodnchild list_pp "Nil_PP" [] ()

**** deprecated
 > hor_or_ver :@ [docs] =
 >   productions $
 >     pp ::= "Hor_or_ver" :@ ["docs" ::: list_pp] :& nilT

 > [ list_pp ::= cons_pp :@ [head_pp, tail_pp]
 >           :|  nil_pp :@ []
 >  ] = grammar $
 >  [ "List_PP" ::= "Cons_PP" :@ [ "head_pp" ::: pp
 >                               , "tail_pp" ::: list_pp] :& nilT
 >              :|  "Nil_PP" :@ [] :& nilT ]

*** Fmts algebras
In the article implementation, `hor_or_ver' is defined in terms
of the format-list primitives. Since we defined them as
attributes, we must compute the AG-algebras.

> fmtsInput child = synAlgs child [ fmts := askE ]
> fmtsBuild = algBuilder (inDesc [pw <-- id]) (project fmts) fmtsInput fmtsOptimA

> empty_fmts  = empty_alg  fmtsBuild
> text_fmts   = text_alg   fmtsBuild
> indent_fmts = indent_alg fmtsBuild
> beside_fmts = beside_alg fmtsBuild
> above_fmts  = above_alg  fmtsBuild
> choice_fmts = choice_alg fmtsBuild

*** Rules
**** List of PP
In the article, `hor_or_ver' is a function

< hor_or_ver :: PW -> [PPDoc] -> Formats

We're implementing `hor_or_ver' as a production of
non-terminal `PP', for each we define the the attribute
`fmts'. In the article, `hor_or_ver' first computes
the lists of formats for each `PPDoc':

< e_fmts = map (doc2fmts pw) es

where

< doc2fmts :: PW -> PPDoc -> Formats
< doc2fmts pw = evalPPDoc (fmts_alg pw)

To do this with attribute grammars, we define the attribute
`fmtss' that computes a list of list of formats, essentially
duplicating the definition of `map'.

> fmtss = attr S "fmtss" (pList (pList pFormat))
> fmtssA = syns fmtss
>  [ nil_pp |- ⟦ [] ⟧
>  , cons_pp |- ⟦ ⟨head_pp!fmts⟩ : ⟨tail_pp!fmtss⟩ ⟧
>  ]

***** Map
The pattern can be abstracted:

> type ListSpec = (Production, Child, Child)

> mapA head_attr map_attr (nil, head, tail) =
>   syns map_attr
>   [ nil  |- ⟦ [] ⟧
>   , cons |- ⟦ ⟨head!head_attr⟩ : ⟨tail!map_attr⟩ ⟧
>   ]
>  where cons = child_prod head

> list_pp_spec = (nil_pp, head_pp, tail_pp)

> fmtssA' = mapA fmts fmtss list_pp_spec

***** Fold
We can generalise mapA:

> foldrA nil_val cons_fun head_attr fold_attr (nil, head, tail) =
>   syns fold_attr
>   [ nil  |- ⟦ nil_val ⟧
>   , cons |- ⟦ cons_fun ⟨head!head_attr⟩ ⟨tail!fold_attr⟩ ⟧
>   ]
>  where cons = child_prod head

MapA can be defined using foldrA:

> mapA' = foldrA [] (:)

Many new combinators can be written using foldrA:

> sumA = foldrA 0 (+)
> allA = foldrA False (&&)

Note that `foldrA' requires one attribute for the head. To
implement `lenghtA' we don't need any attribute, and in other
cases we will need more than one. Can we generalise `foldrA'
to a list of attributes?  Since the attributes have different
types, we must use heterogeneous lists. The will involve some
amount of dependent type programming.

**** hor_or_ver

Thanks to the effectful notation, we are able to write almost
the same definition as in the article. The case expression is
used as a trick in order to have a where clause local to the
effectful brackets.

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
>  ] # fmtssA

** TODO: Frames

* Local variables for emacs
Local Variables:
mode: org
eval: (org-indent-mode -1)
eval: (mmm-mode)
eval: (mmm-ify-by-class 'literate-haskell-bird)
eval: (local-set-key (kbd "<XF86MonBrightnessDown>") 'mmm-parse-buffer)
compile-command: "lhs2TeX --newcode PrettyPrintingExt.lhs > PrettyPrintingExt.hs && cd ../../..; ghc Grammar.SafeAG.Examples.PrettyPrintingExt"
End:
