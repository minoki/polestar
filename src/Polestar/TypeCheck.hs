{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE BangPatterns #-}
module Polestar.TypeCheck where
import Polestar.Type
import Polestar.Subtype
import Data.List
import Control.Monad
import Control.Monad.Fail
import Control.Arrow

-- replaces occurrences of TyRef j, TRef j (j >= i) with TyRef (j + delta), TRef (j + delta)
termShift :: Int -> Int -> Term -> Term
-- termShift 0 i t = t
termShift !delta = go
  where
    go :: Int -> Term -> Term
    go !i t = case t of
      TmPrim _ -> t
      TmAbs name ty body -> TmAbs name (typeShift delta i ty) (go (i + 1) body)
      TmTyAbs name bound body -> TmTyAbs name (typeShift delta i <$> bound) (go (i + 1) body)
      TmRef j | j >= i -> TmRef (j + delta)
              | otherwise -> t
      TmApp u v -> TmApp (go i u) (go i v)
      TmTyApp u t -> TmTyApp (go i u) (typeShift delta i t)
      TmLet name def body -> TmLet name (go i def) (go (i + 1) body)
      TmAlt name tys body -> TmAlt name (typeShift delta i <$> tys) (go (i + 1) body)
      TmIf cond then_ else_ -> TmIf (go i cond) (go i then_) (go i else_)
      TmTuple components -> TmTuple (go i <$> components)
      TmProj tuple j -> TmProj (go i tuple) j
      TmCoerce x ty -> TmCoerce (go i x) (typeShift delta i ty)
      TmCoherentTuple components -> TmCoherentTuple (go i <$> components)

termTypeSubstD :: Int -> Type -> Int -> Term -> Term
termTypeSubstD depth s i t = case t of
  TmPrim _ -> t
  TmAbs name ty body -> TmAbs name (typeSubstD depth s i ty) (termTypeSubstD (depth + 1) s (i + 1) body)
  TmTyAbs name bound body -> TmTyAbs name (typeSubstD depth s i <$> bound) (termTypeSubstD (depth + 1) s (i + 1) body)
  TmRef j | j > i -> TmRef (j - 1)
          | otherwise -> t
  TmApp u v -> TmApp (termTypeSubstD depth s i u) (termTypeSubstD depth s i v)
  TmTyApp u ty -> TmTyApp (termTypeSubstD depth s i u) (typeSubstD depth s i ty)
  TmLet name def body -> TmLet name (termTypeSubstD depth s i def) (termTypeSubstD (depth + 1) s (i + 1) body)
  TmAlt name tys body -> TmAlt name (typeSubstD depth s i <$> tys) (termTypeSubstD (depth + 1) s (i + 1) body)
  TmIf cond then_ else_ -> TmIf (termTypeSubstD depth s i cond) (termTypeSubstD depth s i then_) (termTypeSubstD depth s i else_)
  TmTuple components -> TmTuple (termTypeSubstD depth s i <$> components)
  TmProj tuple j -> TmProj (termTypeSubstD depth s i tuple) j
  TmCoerce x ty -> TmCoerce (termTypeSubstD depth s i x) (typeSubstD depth s i ty)
  TmCoherentTuple components -> TmCoherentTuple (termTypeSubstD depth s i <$> components)

termTypeSubst = termTypeSubstD 0

primTypeOf :: PrimValue -> Type
primTypeOf (PVZero) = TyZero
primTypeOf (PVInt x) | x >= 0 = TyNat
                     | otherwise = TyInt
primTypeOf (PVReal x) | x >= 0 = TyNNReal
                      | otherwise = TyReal
primTypeOf (PVImaginary _) = TyImaginary
primTypeOf (PVComplex _) = TyComplex
primTypeOf (PVBool b) = if b then TyTrue else TyFalse -- TyBool
primTypeOf (PVUnit) = TyUnit
primTypeOf (PVBuiltin f) = case f of
  BNegate -> TyInter [TyZero `TyArr` TyZero
                     ,TyInt `TyArr` TyInt
                     ,TyReal `TyArr` TyReal
                     ,TyImaginary `TyArr` TyImaginary
                     ,TyComplex `TyArr` TyComplex
                     ]
  BLogicalNot -> TyInter [TyTrue `TyArr` TyFalse
                         ,TyFalse `TyArr` TyTrue
                         ,TyBool `TyArr` TyBool
                         ]
  BNatToInt -> TyNat `TyArr` TyInt
  BNatToNNReal -> TyNat `TyArr` TyReal
  BIntToNat -> TyInt `TyArr` TyNat -- max(n,0)
  BIntToReal -> TyInt `TyArr` TyReal
  BNNRealToReal -> TyNNReal `TyArr` TyReal
  BRealToComplex -> TyReal `TyArr` TyComplex
  BMkImaginary -> TyReal `TyArr` TyImaginary
  BImaginaryToComplex -> TyImaginary `TyArr` TyComplex
  BRealPart -> TyInter [TyImaginary `TyArr` TyZero
                       ,TyComplex `TyArr` TyReal
                       ]
  BImagPart -> TyInter [TyReal `TyArr` TyZero
                       ,TyComplex `TyArr` TyReal
                       ]
  BAbs -> TyInter [TyZero `TyArr` TyZero
                  ,TyInt `TyArr` TyNat
                  ,TyComplex `TyArr` TyNNReal
                  ]
  BSqrt -> TyInter [TyZero `TyArr` TyZero
                   ,TyNNReal `TyArr` TyNNReal
                   ,TyComplex `TyArr` TyComplex
                   ]
  BAdd -> TyInter [TyZero `TyArr` (TyZero `TyArr` TyZero)
                  ,TyNat `TyArr` (TyNat `TyArr` TyNat)
                  ,TyInt `TyArr` (TyInt `TyArr` TyInt)
                  ,TyNNReal `TyArr` (TyNNReal `TyArr` TyNNReal)
                  ,TyReal `TyArr` (TyReal `TyArr` TyReal)
                  ,TyImaginary `TyArr` (TyImaginary `TyArr` TyImaginary)
                  ,TyComplex `TyArr` (TyComplex `TyArr` TyComplex)
                  ]
  BSub -> TyInter [TyZero `TyArr` (TyZero `TyArr` TyZero)
                  ,TyNat `TyArr` (TyZero `TyArr` TyNat)
                  ,TyInt `TyArr` (TyInt `TyArr` TyInt)
                  ,TyNNReal `TyArr` (TyZero `TyArr` TyNNReal)
                  ,TyReal `TyArr` (TyReal `TyArr` TyReal)
                  ,TyImaginary `TyArr` (TyImaginary `TyArr` TyImaginary)
                  ,TyComplex `TyArr` (TyComplex `TyArr` TyComplex)
                  ]
  BMul -> TyInter [TyZero `TyArr` (TyComplex `TyArr` TyZero)
                  ,TyComplex `TyArr` (TyZero `TyArr` TyZero)
                  ,TyNat `TyArr` (TyNat `TyArr` TyNat)
                  ,TyInt `TyArr` (TyInt `TyArr` TyInt)
                  ,TyNNReal `TyArr` (TyNNReal `TyArr` TyNNReal)
                  ,TyReal `TyArr` (TyReal `TyArr` TyReal)
                  ,TyImaginary `TyArr` (TyReal `TyArr` TyImaginary)
                  ,TyReal `TyArr` (TyImaginary `TyArr` TyImaginary)
                  ,TyComplex `TyArr` (TyComplex `TyArr` TyComplex)
                  ]
  BDiv -> TyInter [TyNNReal `TyArr` (TyNNReal `TyArr` TyNNReal)
                  ,TyReal `TyArr` (TyReal `TyArr` TyReal)
                  ,TyImaginary `TyArr` (TyReal `TyArr` TyImaginary)
                  ,TyReal `TyArr` (TyImaginary `TyArr` TyImaginary)
                  ,TyImaginary `TyArr` (TyImaginary `TyArr` TyReal)
                  ,TyComplex `TyArr` (TyComplex `TyArr` TyComplex)
                  ]
  BPow -> TyInter [TyComplex `TyArr` (TyZero `TyArr` TyNat {- 1 -})
                  ,TyNat `TyArr` (TyNat `TyArr` TyNat)
                  ,TyInt `TyArr` (TyNat `TyArr` TyInt)
                  -- ,TyInt `TyArr` (TyEvenNat `TyArr` TyNat)
                  -- ,TyReal `TyArr` (TyEvenInt `TyArr` TyNNReal)
                  ,TyNNReal `TyArr` (TyReal `TyArr` TyNNReal)
                  ,TyReal `TyArr` (TyInt `TyArr` TyReal)
                  -- ,TyReal `TyArr` (TyReal `TyArr` TyComplex)
                  ,TyComplex `TyArr` (TyComplex `TyArr` TyComplex)
                  ]
  BTSubNat -> TyNat `TyArr` (TyNat `TyArr` TyNat) -- NNReal?
  BLt -> TyInter [TyNNReal `TyArr` (TyZero `TyArr` TyFalse)
                 ,TyReal `TyArr` (TyReal `TyArr` TyBool)
                 ]
  BLe -> TyInter [TyZero `TyArr` (TyNNReal `TyArr` TyTrue)
                 ,TyReal `TyArr` (TyReal `TyArr` TyBool)
                 ]
  BEqual -> TyComplex `TyArr` (TyComplex `TyArr` TyBool)
  BMax -> TyInter [TyNat `TyArr` (TyInt `TyArr` TyNat)
                  ,TyInt `TyArr` (TyNat `TyArr` TyNat)
                  ,TyInt `TyArr` (TyInt `TyArr` TyInt)
                  ,TyNNReal `TyArr` (TyReal `TyArr` TyNNReal)
                  ,TyReal `TyArr` (TyNNReal `TyArr` TyNNReal)
                  ,TyReal `TyArr` (TyReal `TyArr` TyReal)
                  ]
  BMin -> TyInter [TyZero `TyArr` (TyNNReal `TyArr` TyZero)
                  ,TyNNReal `TyArr` (TyZero `TyArr` TyZero)
                  ,TyNat `TyArr` (TyNat `TyArr` TyNat)
                  ,TyInt `TyArr` (TyInt `TyArr` TyInt)
                  ,TyNNReal `TyArr` (TyNNReal `TyArr` TyNNReal)
                  ,TyReal `TyArr` (TyReal `TyArr` TyReal)
                  ]
  BIntDiv -> TyInter [TyNat `TyArr` (TyNat `TyArr` TyNat)
                     ,TyInt `TyArr` (TyInt `TyArr` TyInt)
                     ]
  BIntMod -> TyInter [TyInt `TyArr` (TyNat `TyArr` TyNat)
                     ,TyInt `TyArr` (TyInt `TyArr` TyInt)
                     ]
  BGcd -> TyInter [TyNat `TyArr` (TyNat `TyArr` TyNat)
                  ,TyInt `TyArr` (TyInt `TyArr` TyNat)
                  ]
  BLcm -> TyInter [TyZero `TyArr` (TyInt `TyArr` TyZero)
                  ,TyInt `TyArr` (TyZero `TyArr` TyZero)
                  ,TyNat `TyArr` (TyNat `TyArr` TyNat)
                  ,TyInt `TyArr` (TyInt `TyArr` TyNat)
                  ]
  BLogicalAnd -> TyInter [TyFalse `TyArr` (TyBool `TyArr` TyFalse)
                         ,TyBool `TyArr` (TyFalse `TyArr` TyFalse)
                         ,TyTrue `TyArr` (TyTrue `TyArr` TyTrue)
                         ,TyBool `TyArr` (TyBool `TyArr` TyBool)
                         ]
  BLogicalOr -> TyInter [TyTrue `TyArr` (TyBool `TyArr` TyTrue)
                        ,TyBool `TyArr` (TyTrue `TyArr` TyTrue)
                        ,TyFalse `TyArr` (TyFalse `TyArr` TyFalse)
                        ,TyBool `TyArr` (TyBool `TyArr` TyBool)
                        ]
  BIterate -> TyAll (Id "a") Nothing $ TyNat `TyArr` (TyRef 1 `TyArr` ((TyRef 2 `TyArr` TyRef 3) `TyArr` TyRef 3))

canonicalTypeOf :: [Binding] -> Term -> Either String CanonicalType
canonicalTypeOf ctx tm = normalizeType ctx <$> typeOf ctx tm

guardWithMessage :: Bool -> e -> Either e ()
guardWithMessage True _ = return ()
guardWithMessage False err = Left err

withMessage :: [a] -> e -> Either e [a]
withMessage [] err = Left err
withMessage xs _ = Right xs

toEitherType :: [Type] -> Either String Type
toEitherType [] = Left "type error"
toEitherType [y] = Right y
toEitherType ys = Right $ TyInter ys

typeOf :: [Binding] -> Term -> Either String Type
typeOf ctx tm = case tm of
  TmPrim primValue -> return (primTypeOf primValue)
  TmAbs name argType body -> do
    let argType' = normalizeType ctx argType
    TyArr argType <$> typeOf (VarBind name argType' : ctx) body
  TmTyAbs name bound body -> do
    let bound' = normalizeTypeM ctx bound
    TyAll name bound <$> typeOf (TyVarBind name bound' : ctx) body
  TmRef i -> return $ typeShift (i + 1) 0 $ getTypeFromContext ctx i
  TmApp f x -> do
    fnType <- canonicalTypeOf ctx f
    actualArgType <- canonicalTypeOf ctx x
    xs <- [ (expectedArgType,retType)
          | CTyArr expectedArgType retType <- exposeTypeC ctx fnType
          ]
      `withMessage` ("invalid function application (expected function type, got: " ++ show fnType ++ ")")
    ys <- [ typeShiftI (-1) 0 retType
          | (expectedArgType,retType) <- xs
          , subTypeC ctx actualArgType expectedArgType
          ]
      `withMessage` ("type error (expected: " ++ concat (intersperse ", " $ map (show . fst) xs) ++ ", got: " ++ show actualArgType ++ ")")
    return $ canonicalToOrdinary ys
  TmTyApp f t -> do
    let t' = normalizeType ctx t
    fnType <- canonicalTypeOf ctx f
    xs <- [ (bound,bodyType)
          | CTyAll _name bound bodyType <- exposeTypeC ctx fnType
          ]
      `withMessage` ("invalid type application (expected forall type, got: " ++ show fnType ++ ")")
    ys <- [ u
          | (bound,bodyType) <- xs
          , subTypeC ctx t' bound
          , u <- typeSubstC t' 0 bodyType
          ]
      `withMessage` ("invalid type application (" ++ show t ++ " is not a subtype of " ++ concat (intersperse ", " $ map (show . fst) xs) ++ ")")
    return $ canonicalToOrdinary ys
  TmLet name def body -> do
    definedType <- canonicalTypeOf ctx def
    typeOf (VarBind name definedType : ctx) body
  TmAlt name tys x -> do
    let gather :: [Either a b] -> Either [a] [b]
        gather (Right x:xs) = Right (x : foldr (const id ||| (:)) [] xs)
        gather (Left err:xs) = left (err:) $ gather xs
        gather [] = Left []
    case gather [typeOf ctx (termTypeSubst ty 0 x) | ty <- tys] of
      Left errors -> Left $ "type alternation failed: " ++ concat (intersperse ", " errors)
      Right ys -> toEitherType ys
  TmIf cond then_ else_ -> do
    condType <- canonicalTypeOf ctx cond
    thenType <- canonicalTypeOf ctx then_
    elseType <- canonicalTypeOf ctx else_
    xs <- [ b
          | b <- exposeTypeC ctx condType
          , subTypeI ctx b CTyBool
          ]
      `withMessage` "if-then-else: conditon must be boolean"
    tys <- joinTypeC ctx thenType elseType
      `withMessage` "if-then-else: incompatible types"
    return $ canonicalToOrdinary $ case (CTyTrue `elem` xs, CTyFalse `elem` xs) of
      (True, True) -> meetTypeC ctx thenType elseType
      (True, _) -> thenType
      (_, True) -> elseType
      _ -> tys
  TmTuple components -> do
    TyTuple <$> mapM (typeOf ctx) components
  TmProj tuple i -> do
    tupleTy <- typeOf ctx tuple
    xs <- [ components
          | TyTuple components <- exposeType ctx tupleTy
          ]
      `withMessage` "expression must be a tuple"
    ys <- [ components !! i
          | components <- xs
          , i < length components
          ]
      `withMessage` "the size of the tuple must be larger than index"
    toEitherType ys
  TmCoerce x t -> do
    let t' = normalizeType ctx t
    xt <- canonicalTypeOf ctx x
    guardWithMessage (subTypeC ctx xt t') ("type coercion: the actual type " ++ show xt ++ " is not a subtype of " ++ show t)
    return t
  TmCoherentTuple components -> do
    componentTypes <- mapM (typeOf ctx) components
    guardWithMessage (length componentTypes >= 2) "coherent tuple: length must be >= 2"
    return $ TyInter componentTypes
