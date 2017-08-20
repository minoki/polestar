{-# LANGUAGE BangPatterns #-}
module Polestar.Subtype where
import Polestar.Type
import Data.Maybe
import Data.Foldable (foldl')
import Control.Monad (zipWithM)

normalizeType :: [Binding] -> Type -> CanonicalType
normalizeType ctx ty = case ty of
  TyPrim p -> [CTyPrim p]
  TyArr u v -> CTyArr (normalizeType ctx u) <$> normalizeType (AnonymousBind : ctx) v
  TyAll name b v -> CTyAll name b' <$> normalizeType (TyVarBind name b' : ctx) v
    where b' = normalizeTypeM ctx b
  TyRef i -> [CTyRef i]
  TyTuple tys -> CTyTuple <$> mapM (normalizeType ctx) tys
  TyInter tys -> foldl' (meetTypeC ctx) [] $ map (normalizeType ctx) tys

normalizeTypeM :: [Binding] -> Maybe Type -> CanonicalType
normalizeTypeM ctx Nothing = []
normalizeTypeM ctx (Just x) = normalizeType ctx x

subTypeC :: [Binding] -> CanonicalType -> CanonicalType -> Bool
subTypeC ctx xs ys = all (\y -> any (\x -> subTypeI ctx x y) xs) ys

-- TODO: formally check the transivity
primSubType :: PrimType -> PrimType -> Bool
primSubType s t | s == t = True
primSubType PTyZero PTyNat = True
primSubType PTyZero PTyInt = True
primSubType PTyZero PTyNNReal = True
primSubType PTyZero PTyReal = True
primSubType PTyZero PTyImaginary = True
primSubType PTyZero PTyComplex = True
primSubType PTyNat PTyInt = True
primSubType PTyNat PTyNNReal = True
primSubType PTyNat PTyReal = True
primSubType PTyNat PTyComplex = True
primSubType PTyInt PTyReal = True
primSubType PTyInt PTyComplex = True
primSubType PTyNNReal PTyReal = True
primSubType PTyNNReal PTyComplex = True
primSubType PTyReal PTyComplex = True
primSubType PTyImaginary PTyComplex = True
primSubType PTyTrue PTyBool = True
primSubType PTyFalse PTyBool = True
primSubType _ _ = False

subTypeI :: [Binding] -> ICanonicalType -> ICanonicalType -> Bool
subTypeI ctx (CTyPrim s) (CTyPrim t) = primSubType s t
subTypeI ctx (CTyArr s0 s1) (CTyArr t0 t1) = subTypeC ctx t0 s0 && subTypeI (AnonymousBind : ctx) s1 t1
subTypeI ctx (CTyTuple c) (CTyTuple c') | length c == length c' = and $ zipWith (subTypeI ctx) c c'
subTypeI ctx (CTyRef i) (CTyRef i') | i == i' = True
subTypeI _ _ _ = False

-- Int /\ NNReal = Nat ?
meetTypeC :: [Binding] -> CanonicalType -> CanonicalType -> CanonicalType
meetTypeC ctx = loop1
  where
    loop1 :: [ICanonicalType] -> [ICanonicalType] -> [ICanonicalType]
    loop1 [] ys = ys
    loop1 (x:xs) ys
      | x' = x : loop1 xs ys'
      | otherwise = loop1 xs ys'
      where (x',ys') = loop2 ys
            -- x' = not (any (\y -> subTypeI ctx y x) ys)
            -- ys' = filter (\y -> not (subTypeI ctx x y)) ys
            loop2 :: [ICanonicalType] -> (Bool,[ICanonicalType])
            loop2 [] = (True,[])
            loop2 (y:ys) | subTypeI ctx x y = loop2 ys -- delete y
                         | subTypeI ctx y x = (False,y:ys) -- delete x
                         | otherwise = (y :) <$> loop2 ys

joinTypeC :: [Binding] -> CanonicalType -> CanonicalType -> CanonicalType
joinTypeC ctx s t
  | subTypeC ctx s t = t
  | subTypeC ctx t s = s
  | otherwise = do s' <- s
                   t' <- t
                   joinTypeI ctx s' t'

-- TODO: formally check the symmetricity
primJoinType :: PrimType -> PrimType -> Maybe PrimType
primJoinType s t | primSubType s t = Just t
                 | primSubType t s = Just s
primJoinType PTyInt PTyNNReal = Just PTyReal
primJoinType PTyNNReal PTyInt = Just PTyReal
primJoinType PTyNat PTyImaginary = Just PTyComplex
primJoinType PTyInt PTyImaginary = Just PTyComplex
primJoinType PTyNNReal PTyImaginary = Just PTyComplex
primJoinType PTyReal PTyImaginary = Just PTyComplex
primJoinType PTyImaginary PTyNat = Just PTyComplex
primJoinType PTyImaginary PTyInt = Just PTyComplex
primJoinType PTyImaginary PTyNNReal = Just PTyComplex
primJoinType PTyImaginary PTyReal = Just PTyComplex
primJoinType PTyTrue PTyFalse = Just PTyBool
primJoinType PTyFalse PTyTrue = Just PTyBool
primJoinType _ _ = Nothing

-- The empty list means Top (universal supertype)
joinTypeI :: [Binding] -> ICanonicalType -> ICanonicalType -> CanonicalType
joinTypeI ctx s t | subTypeI ctx s t = return t
                  | subTypeI ctx t s = return s
joinTypeI ctx (CTyPrim s) (CTyPrim t) = CTyPrim <$> maybeToList (primJoinType s t)
joinTypeI ctx (CTyArr s0 s1) (CTyArr t0 t1) = CTyArr (meetTypeC ctx s0 t0) <$> (joinTypeI (AnonymousBind : ctx) s1 t1)
joinTypeI ctx (CTyTuple xs) (CTyTuple ys) | length xs == length ys = CTyTuple <$> zipWithM (joinTypeI ctx) xs ys
joinTypeI ctx (CTyRef i) t = joinTypeC ctx (typeShiftC (i + 1) 0 (getCBoundFromContext ctx i)) [t]
joinTypeI ctx s (CTyRef i) = joinTypeC ctx [s] (typeShiftC (i + 1) 0 (getCBoundFromContext ctx i))
joinTypeI _ _ _ = []

exposeTypeI :: [Binding] -> ICanonicalType -> CanonicalType
exposeTypeI = exposeTypeD 0
  where
    exposeTypeD :: Int -> [Binding] -> ICanonicalType -> CanonicalType
    exposeTypeD !d ctx (CTyRef i) = concatMap (exposeTypeD (i + d + 1) (drop (i + 1) ctx)) (getCBoundFromContext ctx i)
    exposeTypeD !d ctx t = [typeShiftI d 0 t]

exposeTypeC :: [Binding] -> CanonicalType -> CanonicalType
exposeTypeC ctx tys = tys >>= exposeTypeI ctx

exposeType :: [Binding] -> Type -> [Type]
exposeType = exposeTypeD 0
  where
    exposeTypeD :: Int -> [Binding] -> Type -> [Type]
    exposeTypeD !d ctx (TyRef i) = case getBoundFromContext ctx i of
      Nothing -> []
      Just ty -> exposeTypeD (i + d + 1) (drop (i + 1) ctx) ty
    exposeTypeD !d ctx (TyInter tys) = concatMap (exposeTypeD d ctx) tys
    exposeTypeD !d ctx t = [typeShift d 0 t]
