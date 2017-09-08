{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE BangPatterns #-}
module Polestar.Core.TypeCheck where
import Polestar.Core.Type
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
      TmRef j | j >= i -> TmRef (j + delta)
              | otherwise -> t
      TmApp u v -> TmApp (go i u) (go i v)
      TmLet name def body -> TmLet name (go i def) (go (i + 1) body)
      TmIf cond then_ else_ -> TmIf (go i cond) (go i then_) (go i else_)
      TmTuple components -> TmTuple (go i <$> components)
      TmProj tuple j -> TmProj (go i tuple) j
      TmIterate n init succ -> TmIterate (go i n) (go i init) (go i succ)

termTypeSubstD :: Int -> Type -> Int -> Term -> Term
termTypeSubstD depth s i t = case t of
  TmPrim _ -> t
  TmAbs name ty body -> TmAbs name (typeSubstD depth s i ty) (termTypeSubstD (depth + 1) s (i + 1) body)
  TmRef j | j > i -> TmRef (j - 1)
          | otherwise -> t
  TmApp u v -> TmApp (termTypeSubstD depth s i u) (termTypeSubstD depth s i v)
  TmLet name def body -> TmLet name (termTypeSubstD depth s i def) (termTypeSubstD (depth + 1) s (i + 1) body)
  TmIf cond then_ else_ -> TmIf (termTypeSubstD depth s i cond) (termTypeSubstD depth s i then_) (termTypeSubstD depth s i else_)
  TmTuple components -> TmTuple (termTypeSubstD depth s i <$> components)
  TmProj tuple j -> TmProj (termTypeSubstD depth s i tuple) j
  TmIterate n init succ -> TmIterate (termTypeSubstD depth s i n) (termTypeSubstD depth s i init) (termTypeSubstD depth s i succ)

termTypeSubst = termTypeSubstD 0

primTypeOf :: PrimValue -> Type
primTypeOf (PVNat x) = TyNat
primTypeOf (PVInt x) = TyInt
primTypeOf (PVReal x) = TyReal
primTypeOf (PVBool b) = TyBool
primTypeOf (PVUnit) = TyUnit
primTypeOf (PVUnary f) = case f of
  UNegateInt -> TyInt `TyArr` TyInt
  UNegateReal -> TyReal `TyArr` TyReal
  UNatToInt -> TyNat `TyArr` TyInt
  UIntToReal -> TyInt `TyArr` TyReal
  UIntToNat -> TyInt `TyArr` TyNat
primTypeOf (PVBinary f) = case f of
  UAddNat -> TyNat `TyArr` (TyNat `TyArr` TyNat)
  UMulNat -> TyNat `TyArr` (TyNat `TyArr` TyNat)
  UTSubNat -> TyNat `TyArr` (TyNat `TyArr` TyNat)
  UPowNatNat -> TyNat `TyArr` (TyNat `TyArr` TyNat)
  UEqualNat -> TyNat `TyArr` (TyNat `TyArr` TyBool)
  ULessThanNat -> TyNat `TyArr` (TyNat `TyArr` TyBool)
  ULessEqualNat -> TyNat `TyArr` (TyNat `TyArr` TyBool)

  UAddInt -> TyInt `TyArr` (TyInt `TyArr` TyInt)
  USubInt -> TyInt `TyArr` (TyInt `TyArr` TyInt)
  UMulInt -> TyInt `TyArr` (TyInt `TyArr` TyInt)
  UPowIntNat -> TyInt `TyArr` (TyNat `TyArr` TyInt)
  UEqualInt -> TyInt `TyArr` (TyInt `TyArr` TyBool)
  ULessThanInt -> TyInt `TyArr` (TyInt `TyArr` TyBool)
  ULessEqualInt -> TyInt `TyArr` (TyInt `TyArr` TyBool)

  UAddReal -> TyReal `TyArr` (TyReal `TyArr` TyReal)
  USubReal -> TyReal `TyArr` (TyReal `TyArr` TyReal)
  UMulReal -> TyReal `TyArr` (TyReal `TyArr` TyReal)
  UDivReal -> TyReal `TyArr` (TyReal `TyArr` TyReal)
  UPowRealReal -> TyReal `TyArr` (TyReal `TyArr` TyReal)
  UEqualReal -> TyReal `TyArr` (TyReal `TyArr` TyBool)
  ULessThanReal -> TyReal `TyArr` (TyReal `TyArr` TyBool)
  ULessEqualReal -> TyReal `TyArr` (TyReal `TyArr` TyBool)

guardWithMessage :: Bool -> e -> Either e ()
guardWithMessage True _ = return ()
guardWithMessage False err = Left err

typeOf :: [Binding] -> Term -> Either String Type
typeOf ctx tm = case tm of
  TmPrim primValue -> return (primTypeOf primValue)
  TmAbs name argType body -> do
    TyArr argType <$> typeOf (VarBind name argType : ctx) body
  TmRef i -> return $ typeShift (i + 1) 0 $ getTypeFromContext ctx i
  TmApp f x -> do
    fnType <- typeOf ctx f
    actualArgType <- typeOf ctx x
    case fnType of
      TyArr expectedArgType retType | expectedArgType == actualArgType -> return $ typeShift (-1) 0 retType
                                    | otherwise -> Left ("type error (expected: " ++ show expectedArgType ++ ", got: " ++ show actualArgType ++ ")")
      _ -> Left ("invalid function application (expected function type, got: " ++ show fnType ++ ")")
  TmLet name def body -> do
    definedType <- typeOf ctx def
    typeOf (VarBind name definedType : ctx) body
  TmIf cond then_ else_ -> do
    condType <- typeOf ctx cond
    thenType <- typeOf ctx then_
    elseType <- typeOf ctx else_
    guardWithMessage (condType == TyBool) "if-then-else: conditon must be boolean"
    guardWithMessage (thenType == elseType) "if-then-else: incompatible types"
    return thenType
  TmTuple components -> do
    TyTuple <$> mapM (typeOf ctx) components
  TmProj tuple i -> do
    tupleTy <- typeOf ctx tuple
    case tupleTy of
      TyTuple components | i < length components -> return (components !! i)
                         | otherwise -> Left "the size of the tuple must be larger than index"
      _ -> Left "expression must be a tuple"
  TmIterate n init succ -> do
    nTy <- typeOf ctx n
    guardWithMessage (nTy == TyNat) "iterate: count must be a natural number"
    initTy <- typeOf ctx init
    succTy <- typeOf ctx succ
    let expectedSuccTy = TyArr initTy (typeShift 1 0 initTy)
    guardWithMessage (succTy == expectedSuccTy) ("iterate: succ function must be " ++ show expectedSuccTy)
    guardWithMessage (isScalarType initTy) ("iterate: non-scalar accumulator type is not supported")
    return initTy
