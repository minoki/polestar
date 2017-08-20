{-# LANGUAGE BangPatterns #-}
module Polestar.Eval
  (termShift
  ,termTypeSubst
  ,termSubstD
  ,termSubst
  ,ValueBinding(..)
  ,getValueFromContext
  ,eval1
  ,eval
  ) where
import Polestar.Type
import Polestar.TypeCheck
import Data.Complex

termSubstD :: Int -> Term -> Int -> Term -> Term
termSubstD !depth s !i t = case t of
  TmAbs name ty body -> TmAbs name (typeShift (-1) i ty) (termSubstD depth s (i + 1) body)
  TmTyAbs name bound body -> TmTyAbs name (typeShift (-1) i <$> bound) (termSubstD depth s (i + 1) body)
  TmRef j | j == i -> termShift depth 0 s
          | j > i -> TmRef (j - 1)
          | otherwise -> t
  TmApp u v -> TmApp (termSubstD depth s i u) (termSubstD depth s i v)
  TmTyApp u t -> TmTyApp (termSubstD depth s i u) (typeShift (-1) i t)
  TmLet name def body -> TmLet name (termSubstD depth s i def) (termSubstD depth s (i + 1) body) -- ?
  TmIf cond then_ else_ -> TmIf (termSubstD depth s i cond) (termSubstD depth s i then_) (termSubstD depth s i else_)
  TmPrim _ -> t
  TmCoerce x ty  -> TmCoerce (termSubstD depth s i x) (typeShift (-1) i ty)
  TmAlt name tys body -> TmAlt name (map (typeShift (-1) i) tys) (termSubstD depth s (i + 1) body)
  TmTuple components -> TmTuple $ termSubstD depth s i <$> components
  TmProj tuple j -> TmProj (termSubstD depth s i tuple) j
  TmCoherentTuple components -> TmCoherentTuple $ termSubstD depth s i <$> components

-- replaces occurrences of TRef j (j > i) with TRef (j-1), and TRef i with the given term
termSubst = termSubstD 0

natFromValue :: Term -> Either String Integer
natFromValue (TmPrim (PVZero)) = return 0
natFromValue (TmPrim (PVInt x)) | x >= 0 = return x
natFromValue _ = Left "type error (expected a natural number)"

intFromValue :: Term -> Either String Integer
intFromValue (TmPrim (PVZero)) = return 0
intFromValue (TmPrim (PVInt x)) = return x
intFromValue _ = Left "type error (expected an integer)"

realFromValue :: Term -> Either String Double
realFromValue (TmPrim (PVZero)) = return 0
realFromValue (TmPrim (PVInt x)) = return (fromIntegral x)
realFromValue (TmPrim (PVReal x)) = return x
realFromValue _ = Left "type error (expected a real number)"

imaginaryFromValue :: Term -> Either String Double
imaginaryFromValue (TmPrim (PVZero)) = return 0
imaginaryFromValue (TmPrim (PVImaginary x)) = return x
imaginaryFromValue _ = Left "type error (expected a real number)"

applyBuiltinUnary :: Builtin -> Term -> Either String Term
applyBuiltinUnary f v = case f of
  BNegate -> case v of
    TmPrim PVZero -> return v
    TmPrim (PVInt x) -> return (TmPrim $ PVInt $ negate x)
    TmPrim (PVReal x) -> return (TmPrim $ PVReal $ negate x)
    TmPrim (PVImaginary x) -> return (TmPrim $ PVImaginary $ negate x)
    TmPrim (PVComplex x) -> return (TmPrim $ PVComplex $ negate x)
    _ -> Left "type error (expected an integer or a real number)"
  BNatToInt -> (TmPrim . PVInt) <$> natFromValue v
  BNatToNNReal -> (TmPrim . PVReal . fromIntegral) <$> natFromValue v
  BIntToNat -> (\x -> if x >= 0 then TmPrim (PVInt x) else TmPrim PVZero) <$> intFromValue v
  BIntToReal -> (TmPrim . PVReal . fromIntegral) <$> intFromValue v
  BNNRealToReal -> (TmPrim . PVReal) <$> realFromValue v
  BRealToComplex -> (TmPrim . PVComplex . (:+0)) <$> realFromValue v
  BMkImaginary -> (TmPrim . PVImaginary) <$> realFromValue v
  BImaginaryToComplex -> (TmPrim . PVComplex . (0:+)) <$> imaginaryFromValue v
  _ -> Left "applyBuiltinUnary: not unary"

applyBuiltinBinary :: Builtin -> Term -> Term -> Either String Term
applyBuiltinBinary f u v = case f of
  BDiv -> (TmPrim . PVReal) <$> ((/) <$> realFromValue u <*> realFromValue v)
  BLt -> (TmPrim . PVBool) <$> ((<) <$> realFromValue u <*> realFromValue v)
  BLe -> (TmPrim . PVBool) <$> ((<=) <$> realFromValue u <*> realFromValue v)
  BEqual -> (TmPrim . PVBool) <$> ((==) <$> realFromValue u <*> realFromValue v)
  BAdd -> case (TmPrim . PVInt) <$> ((+) <$> intFromValue u <*> intFromValue v) of
    Left _ -> (TmPrim . PVReal) <$> ((+) <$> realFromValue u <*> realFromValue v)
    Right w -> return w
  BSub -> case (TmPrim . PVInt) <$> ((-) <$> intFromValue u <*> intFromValue v) of
    Left _ -> (TmPrim . PVReal) <$> ((-) <$> realFromValue u <*> realFromValue v)
    Right w -> return w
  BMul -> case (TmPrim . PVInt) <$> ((*) <$> intFromValue u <*> intFromValue v) of
    Left _ -> (TmPrim . PVReal) <$> ((*) <$> realFromValue u <*> realFromValue v)
    Right w -> return w

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
  TmTyAbs _ _ _ -> return t
  TmRef i -> return $ getValueFromContext ctx i
  TmApp u v
    | isValue u && isValue v -> case u of
        TmAbs _name _ty body -> return $ termSubst v 0 body -- no type checking here
        TmPrim (PVBuiltin f) | arity f == 1-> applyBuiltinUnary f v
        TmPrim (PVBuiltin _) -> return t -- partial application
        TmApp (TmPrim (PVBuiltin f)) u' | arity f == 2 -> applyBuiltinBinary f u' v
        _ -> Left "invalid function application (expected function type)"
    | isValue u -> TmApp u <$> (eval1 ctx v)
    | otherwise -> TmApp <$> (eval1 ctx u) <*> pure v
  TmTyApp u ty
    | isValue u -> case u of
        TmTyAbs _name _bound body -> return $ termTypeSubst ty 0 body
        _ -> Left "invalid type application (expected forall type)"
    | otherwise -> TmTyApp <$> eval1 ctx u <*> pure ty
  TmLet name def body
    | isValue def -> return $ termSubst def 0 body
    | otherwise -> TmLet name <$> eval1 ctx def <*> pure body
  TmIf cond then_ else_
    | isValue cond -> case cond of
        TmPrim (PVBool True) -> return then_  -- no type checking here
        TmPrim (PVBool False) -> return else_ -- no type checking here
        _ -> Left "if-then-else: condition must be boolean"
    | otherwise -> TmIf <$> (eval1 ctx cond) <*> pure then_ <*> pure else_
  TmCoerce x ty
    | isValue x -> return x
    | otherwise -> TmCoerce <$> eval1 ctx x <*> pure ty
  TmAlt name tys x
    | isValue x -> return $ termTypeSubst TyUnit 0 x -- dummy type
    | otherwise -> TmAlt name tys <$> eval1 ctx x
  TmTuple components -> case span isValue components of
    (_,[]) -> return t
    (v,w:ws) -> eval1 ctx w >>= \w' -> return (TmTuple (v ++ (w':ws)))
  TmProj tuple j
    | isValue tuple -> case tuple of
        TmTuple components | length components > j -> return $ components !! j
                           | otherwise -> Left "tuple too short"
        _ -> Left "projection: not a tuple"
    | otherwise -> TmProj <$> eval1 ctx tuple <*> pure j
  TmCoherentTuple components -> Left "coherenet tuple: not supported yet"

eval :: [ValueBinding] -> Term -> Either String Term
eval ctx t | isValue t = return t
           | otherwise = eval1 ctx t >>= eval ctx
