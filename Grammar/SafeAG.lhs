* Overview
This file is licensed under GPL v3.

EDSL for attribute grammars in Haskell.

This library defines first-class attribute grammars
objects. This allows to write compilers modularly.  Our
approach is distinct to the previous attempts in that it is
both lightweight and type safe.

Other first-class implementation of attribute grammars in
Haskell are:

- [Moor] :: Light-weight approach with no type safety.
- [Viera] :: Type-safe approach with complex types and classes.
- [Balestrieri] :: Type-safe approach with complex types and classes.

Our lightweight approach ensures a clean public interface for
the user with simple types and simple error messages that do
not leak implementation details, unlike [Viera] and
[Balestrieri]. In addition, the grammars are thoroughly
checked unlike with the simple approach of [Moor].

To achieve this, our approach involves two typechecking
phases.  This first is the static typechecking by the
compiler where the type of attributes and their kind
(inherited, synthesized, or terminals) is checked
statically. The second phase checks that the attribtion rules
are complete for a given grammar, that the concrete tree type
is compatible with the grammar, and that the concrete input
and output types are compatible with the attribution rules.
This second phase occurs at runtime, however it should not be
confused with dynamic typing: in contrast, the runtime
typechecking is done once and for all, whereas dynamic typing
involves doing testing the types every time a function is
used and may fail if the type mismatch. However with runtime
typechecking, if a function passes the tests, we have the
certainty that no type error will be the cause for failure
when executing that function.

** Bibliography

- **[Moor]**
  Oege De Moor, Kevin Backhouse, S. Doaitse Swierstra,
  /First-class Attribute Grammars/,
  Informatica, 2000.

- **[Viera]**
  Marcos Viera, Swierstra, S. Doaitse Swierstra, Wouter Swierstra,
  /Attribute Grammars Fly First-class: How to Do Aspect Oriented Programming in Haskell/,
  ICFP 2009.

- **[Balestrieri]**
  Florent Balestrieri,
  /The productivity of polymorphic stream equations and the composition of circular traversals/,
  University of Nottingham, 2015.

** Dependencies
ghc-8.0.1
mtl-2.2.1

* Header
** Module Exports

- when using the library primitives, the user should never
  SEE any `Dynamic', always concrete types.
- the user should never SEE Attribute, only `Attr k a'

> module Grammar.SafeAG
>  ( module Grammar.SafeAG.Core
>  , module Grammar.SafeAG.CFG
>  , module Grammar.SafeAG.GramDesc ) where
>  import Grammar.SafeAG.Core hiding (production, Terminals, consT, nilT)
>  import Grammar.SafeAG.CFG
>  import Grammar.SafeAG.GramDesc
