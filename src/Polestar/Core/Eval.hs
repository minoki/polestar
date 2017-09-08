{-# LANGUAGE BangPatterns #-}
module Polestar.Core.Eval
  (termShift
  ,termTypeSubst
  ,termSubstD
  ,termSubst
  ,ValueBinding(..)
  ,getValueFromContext
  ,eval1
  ,eval
  ) where
import Polestar.Core.Type
import Polestar.Core.TypeCheck
import Data.Complex
import GHC.Float (expm1, log1p)

termSubstD :: Int -> Term -> Int -> Term -> Term
termSubstD !depth s !i t = case t of
  TmAbs name ty body -> TmAbs name (typeShift (-1) i ty) (termSubstD depth s (i + 1) body)
  TmRef j | j == i -> termShift depth 0 s
          | j > i -> TmRef (j - 1)
          | otherwise -> t
  TmApp u v -> TmApp (termSubstD depth s i u) (termSubstD depth s i v)
  TmLet name def body -> TmLet name (termSubstD depth s i def) (termSubstD depth s (i + 1) body) -- ?
  TmIf cond then_ else_ -> TmIf (termSubstD depth s i cond) (termSubstD depth s i then_) (termSubstD depth s i else_)
  TmPrim _ -> t
  TmTuple components -> TmTuple $ termSubstD depth s i <$> components
  TmProj tuple j -> TmProj (termSubstD depth s i tuple) j
  TmIterate n init succ -> TmIterate (termSubstD depth s i n) (termSubstD depth s i init) (termSubstD depth s i succ)

-- replaces occurrences of TRef j (j > i) with TRef (j-1), and TRef i with the given term
termSubst = termSubstD 0

natFromValue :: Term -> Either String Integer
natFromValue (TmPrim (PVNat x)) = return x
natFromValue x = Left ("type error (expected a natural number, but got " ++ show x ++ ")")

intFromValue :: Term -> Either String Integer
intFromValue (TmPrim (PVInt x)) = return x
intFromValue x = Left ("type error (expected an integer, but got " ++ show x ++ ")")

realFromValue :: Term -> Either String Double
realFromValue (TmPrim (PVReal x)) = return x
realFromValue x = Left ("type error (expected a real number, but got " ++ show x ++ ")")

boolFromValue :: Term -> Either String Bool
boolFromValue (TmPrim (PVBool x)) = return x
boolFromValue x = Left ("type error (expected a boolean, but got " ++ show x ++ ")")

applyBuiltinUnary :: UnaryFn -> Term -> Either String Term
applyBuiltinUnary f v = case f of
  UNegateInt -> (TmPrim . PVInt) <$> intFromValue v
  UNegateReal -> (TmPrim . PVReal) <$> realFromValue v
  UNatToInt -> (TmPrim . PVInt) <$> natFromValue v
  UIntToReal -> (TmPrim . PVReal . fromInteger) <$> intFromValue v
  UIntToNat -> (TmPrim . PVNat . max 0) <$> intFromValue v

applyBuiltinBinary :: BinaryFn -> Term -> Term -> Either String Term
applyBuiltinBinary f u v = case f of
  UAddNat -> (TmPrim . PVNat) <$> ((+) <$> natFromValue u <*> natFromValue v)
  UMulNat -> (TmPrim . PVNat) <$> ((*) <$> natFromValue u <*> natFromValue v)
  UTSubNat -> (TmPrim . PVNat . max 0) <$> ((-) <$> natFromValue u <*> natFromValue v)
  UPowNatNat -> (TmPrim . PVNat) <$> ((^) <$> natFromValue u <*> natFromValue v)
  UEqualNat -> (TmPrim . PVBool) <$> ((==) <$> natFromValue u <*> natFromValue v)
  ULessThanNat -> (TmPrim . PVBool) <$> ((<) <$> natFromValue u <*> natFromValue v)
  ULessEqualNat -> (TmPrim . PVBool) <$> ((<=) <$> natFromValue u <*> natFromValue v)
  UAddInt -> (TmPrim . PVInt) <$> ((+) <$> intFromValue u <*> intFromValue v)
  USubInt -> (TmPrim . PVInt) <$> ((-) <$> intFromValue u <*> intFromValue v)
  UMulInt -> (TmPrim . PVInt) <$> ((*) <$> intFromValue u <*> intFromValue v)
  UPowIntNat -> (TmPrim . PVInt) <$> ((^) <$> intFromValue u <*> natFromValue v)
  UEqualInt -> (TmPrim . PVBool) <$> ((==) <$> intFromValue u <*> intFromValue v)
  ULessThanInt -> (TmPrim . PVBool) <$> ((<) <$> intFromValue u <*> intFromValue v)
  ULessEqualInt -> (TmPrim . PVBool) <$> ((<=) <$> intFromValue u <*> intFromValue v)
  UAddReal -> (TmPrim . PVReal) <$> ((+) <$> realFromValue u <*> realFromValue v)
  USubReal -> (TmPrim . PVReal) <$> ((-) <$> realFromValue u <*> realFromValue v)
  UMulReal -> (TmPrim . PVReal) <$> ((*) <$> realFromValue u <*> realFromValue v)
  UDivReal -> (TmPrim . PVReal) <$> ((/) <$> realFromValue u <*> realFromValue v)
  UPowRealReal -> (TmPrim . PVReal) <$> ((**) <$> realFromValue u <*> realFromValue v)
  UEqualReal -> (TmPrim . PVBool) <$> ((==) <$> realFromValue u <*> realFromValue v)
  ULessThanReal -> (TmPrim . PVBool) <$> ((<) <$> realFromValue u <*> realFromValue v)
  ULessEqualReal -> (TmPrim . PVBool) <$> ((<=) <$> realFromValue u <*> realFromValue v)

data ValueBinding = ValueBind !Term
                  | TypeBind
                  deriving (Eq,Show)

getValueFromContext :: [ValueBinding] -> Int -> Term
getValueFromContext ctx i
  | i < length ctx = case ctx !! i of
                       ValueBind x -> x
                       b -> error ("TRef: expected a variable binding, found " ++ show b)
  | otherwise = error "TRef: index out of bounds"

eval1 :: [ValueBinding] -> Term -> Either String Term
eval1 ctx t = case t of
  TmPrim _ -> return t
  TmAbs _ _ _ -> return t
  TmRef i -> return $ getValueFromContext ctx i
  TmApp u v
    | isValue u && isValue v -> case u of
        TmAbs _name _ty body -> return $ termSubst v 0 body -- no type checking here
        TmPrim (PVUnary f) -> applyBuiltinUnary f v
        TmPrim (PVBinary _) -> return t -- partial application
        TmApp (TmPrim (PVBinary f)) u' -> applyBuiltinBinary f u' v
        _ -> Left "invalid function application (expected function type)"
    | isValue u -> TmApp u <$> (eval1 ctx v)
    | otherwise -> TmApp <$> (eval1 ctx u) <*> pure v
  TmLet name def body
    | isValue def -> return $ termSubst def 0 body
    | otherwise -> TmLet name <$> eval1 ctx def <*> pure body
  TmIf cond then_ else_
    | isValue cond -> case cond of
        TmPrim (PVBool True) -> return then_  -- no type checking here
        TmPrim (PVBool False) -> return else_ -- no type checking here
        _ -> Left "if-then-else: condition must be boolean"
    | otherwise -> TmIf <$> (eval1 ctx cond) <*> pure then_ <*> pure else_
  TmTuple components -> case span isValue components of
    (_,[]) -> return t
    (v,w:ws) -> eval1 ctx w >>= \w' -> return (TmTuple (v ++ (w':ws)))
  TmProj tuple j
    | isValue tuple -> case tuple of
        TmTuple components | length components > j -> return $ components !! j
                           | otherwise -> Left "tuple too short"
        _ -> Left "projection: not a tuple"
    | otherwise -> TmProj <$> eval1 ctx tuple <*> pure j
  TmIterate n init succ
    | isValue n && isValue init && isValue succ -> do
        n' <- natFromValue n
        if n' == 0
          then return $ init
          else return $ TmIterate (TmPrim (PVNat (n' - 1))) (TmApp succ init) succ
    | isValue n && isValue init -> TmIterate n init <$> eval1 ctx succ
    | isValue n -> TmIterate n <$> eval1 ctx init <*> pure succ
    | otherwise -> TmIterate <$> eval1 ctx n <*> pure init <*> pure succ

eval :: [ValueBinding] -> Term -> Either String Term
eval ctx t | isValue t = return t
           | otherwise = eval1 ctx t >>= eval ctx
