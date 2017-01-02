{-# LANGUAGE TemplateHaskell, QuasiQuotes, LambdaCase #-}

{-| 'effectful' implements a generalisation of idiom brackets
that relies on types to insert @pure@ and @<*>@ in the right
places.  With this approach there is no need for nested idiom
brackets.  Unfortunately, it is currently of limited utility
because template haskell only knows the types of the imported
names.  The types of local definitions are unknown, which
will cause a compile time error if they are used in an
'effectful' expression.  Hopefully a dedicated compiler
extension will be provided eventually.

-}

{-|

@$('effectful' f exp)@ is a template haskell splice that
inserts @pure@ and @<*>@ in the right places inside @exp@ to
ensure that the result has type @f a@ for some type @a@.

Example use, given @a, b :: Maybe Int@, @f :: Int -> Maybe Int@

@
$(effectful [t|Maybe|] [| a + b + f 2 + 3 |]) :: Maybe Int
@

-}

effectful fq eq = do
  f <- fq; e <- eq
  (e,t) <- idiomize f e
  if impure f t
    then return e
    else [| pure $(r e) |]

{-|

`idiomize' is type-guided transformation, that adds @pure@
and @<*>@ in the right places to make the expression
typecheck.  The @Type@ argument is the applicative functor.
The result is a pair of the transformed expression and the
inferred type. Which can be pure or impure.  Impure means
that it is in the applicative functor.

-}

idiomize :: Type -> Exp -> Q (Exp, Type)

idiomize f e@(VarE n) = do
  info <- reify n
  return $ case info of
    VarI _ ty _ -> (e, ty)
    ClassOpI _ ty _ -> (e, ty)
    _ -> undefined

idiomize f e@(ConE n) = do
  info <- reify n
  return $ case info of
    DataConI _ ty _ -> (e, ty)
    _ -> undefined

idiomize f e@(LitE l) = do {t <- lit_type l; return (e, t) }

idiomize f e@(InfixE Nothing (VarE n) Nothing) = do
  info <- reify n
  return $ case info of
    VarI _ ty _ -> (e, ty)
    ClassOpI _ ty _ -> (e, ty)
    _ -> undefined

idiomize f e@(InfixE Nothing (ConE n) Nothing) = do
  info <- reify n
  return $ case info of
    DataConI _ ty _ -> (e, ty)
    _ -> undefined

idiomize f (AppE x y) = do
  (xe, xt) <- idiomize f x
  (ye, yt) <- idiomize f y
  case (impure f xt, impure f yt) of
   (False, False) -> do
     e <- [e| $(r xe) $(r ye) |]
     let t = app xt yt
     return (e,t)
   (False, True) -> do
     e <- [e| $(r xe) <$> $(r ye) |]
     let t = AppT f (app xt (obj f yt))
     return (e,t)
   (True, False) -> do
     e <- [e| ($ $(r ye)) <$> $(r xe) |]
     let t = AppT f (app (obj f xt) yt)
     return (e,t)
   (True, True) -> do
     e <- [e| $(r xe) <*> $(r ye) |]
     let t = AppT f (app (obj f xt) (obj f yt))
     return (e,t)

idiomize f (InfixE (Just left) op (Just right)) = do
  n <- newName "x"
  let e = (InfixE Nothing op Nothing `AppE` left) `AppE` right
  idiomize f e

idiomize f (CondE c t e) =
  idiomize f =<< [e| ifThenElse $(r c) $(r t) $(r e) |]

idiomize f t = error $ "idiomize (" ++ show f ++ ") (" ++ show t ++ ")"

-- |impure f t| is true if |t| is of the form |f a| for some |a|.

impure :: Type -> Type -> Bool
impure f (AppT g x) | f == g = True
impure _ _ = False

-- |obj f (f x) == x|
obj :: Type -> Type -> Type
obj f (AppT g t) | f == g = t
obj _ _ = undefined

-- Apply a function type to the domain type
app :: Type -> Type -> Type
app (AppT (AppT ArrowT a) b) x = subst (unif x a) b
app (ForallT xs _ a) b = app a b
app x y = error $ "app (" ++ show x ++ ") (" ++ show y ++ ")"

unif x a | x == a  =  M.empty
unif x (VarT n) = M.singleton n x
unif (AppT x y) (AppT x' y') =
  M.union (unif x x') (unif y y')
unif x y = error $ "unif (" ++ show x ++ ") (" ++ show y ++ ")"

subst s t@(VarT n) = maybe t id (M.lookup n s)
subst s (AppT x y) = AppT (subst s x) (subst s y)
subst s t = t


lit_type :: Lit -> TypeQ
lit_type = \case
  CharL       _ -> [t| Char     |]
  StringL     _ -> [t| String   |]
  IntegerL    _ -> [t| Integer  |]
  RationalL   _ -> [t| Rational |]
  IntPrimL    _ -> [t| Integer  |]
  WordPrimL   _ -> [t| Integer  |]
  FloatPrimL  _ -> [t| Rational |]
  DoublePrimL _ -> [t| Rational |]
  StringPrimL _ -> [t| [Word8]  |]
  CharPrimL   _ -> [t| Char     |]

{-
Local Variables:
compile-command: "ghc Effectful"
End:
-}
