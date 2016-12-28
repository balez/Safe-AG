The type Unknown is used for debugging.

> {-# LANGUAGE
>    Rank2Types
> #-}

> module Grammar.SafeAG.Unknown where

`ExpectedTypeOf` and `inferredTypeOf` are used in the
interactive session to obtain type information from the
typechecker.

> data Unknown = ExpectedTypeOf {inferredTypeOf :: forall a . a}
> expectedTypeOf = ExpectedTypeOf
