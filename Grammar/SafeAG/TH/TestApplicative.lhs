%include lhs2TeX.fmt
%include applicative.fmt

\begin{code}
{-# LANGUAGE  QuasiQuotes, TemplateHaskell, PatternGuards #-}
module Grammar.SafeAG.TH.TestApplicative where
import Grammar.SafeAG.TH.Applicative


-- Local function depending on external effectful value.

test_let1 a b c = ⟦
  let f x y = x + ⟨c⟩ * y
      z = ⟨a⟩
  in f ⟨b⟩ z
   ⟧

-- Wrong use of locally bound variables inside effectful brackets

-- err_clause a = ⟦
--   let f (x, y) = x + ⟨y⟩
--   in f a
--    ⟧

err_clause a = ⟦
  let f z | (x, y) <- z = x + ⟨y⟩
  in f a
   ⟧

err_let a = ⟦ let (x,y) = a in ⟨x⟩ + y ⟧

err_where a = ⟦
 let it = ⟨x⟩ + y where (x,y) = a
  in it
 ⟧

err_match a = ⟦ case a of (x, y) -> ⟨x⟩ + y ⟧

err_lam a = ⟦ (\(x,y) -> ⟨x⟩ + y) a ⟧

err_scope1 a b = ⟦ f ⟨a⟩ ⟨b⟩ ⟧

{-
Local Variables:
compile-command: "lhs2TeX --newcode TestApplicative.lhs > TestApplicative.hs && cd ../../..; ghc Grammar.SafeAG.TH.TestApplicative"
End:
-}
\end{code}
