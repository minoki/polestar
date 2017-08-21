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

nnrealFromValue :: Term -> Either String Double
nnrealFromValue (TmPrim (PVZero)) = return 0
nnrealFromValue (TmPrim (PVInt x)) | x >= 0 = return (fromIntegral x)
nnrealFromValue (TmPrim (PVReal x)) | x >= 0 = return x
nnrealFromValue _ = Left "type error (expected a non-negative real number)"

realFromValue :: Term -> Either String Double
realFromValue (TmPrim (PVZero)) = return 0
realFromValue (TmPrim (PVInt x)) = return (fromIntegral x)
realFromValue (TmPrim (PVReal x)) = return x
realFromValue _ = Left "type error (expected a real number)"

imaginaryFromValue :: Term -> Either String Double
imaginaryFromValue (TmPrim (PVZero)) = return 0
imaginaryFromValue (TmPrim (PVImaginary x)) = return x
imaginaryFromValue _ = Left "type error (expected an imaginary number)"

complexFromValue :: Term -> Either String (Complex Double)
complexFromValue (TmPrim (PVZero)) = return 0
complexFromValue (TmPrim (PVInt x)) = return (fromIntegral x)
complexFromValue (TmPrim (PVReal x)) = return (x:+0)
complexFromValue (TmPrim (PVImaginary x)) = return (0:+x)
complexFromValue (TmPrim (PVComplex z)) = return z
complexFromValue _ = Left "type error (expected a complex number)"

boolFromValue :: Term -> Either String Bool
boolFromValue (TmPrim (PVBool x)) = return x
boolFromValue _ = Left "type error (expected a boolean)"

applyBuiltinUnary :: Builtin -> Term -> Either String Term
applyBuiltinUnary f v = case f of
  BNegate -> case v of
    TmPrim PVZero -> return v
    TmPrim (PVInt x) -> return (TmPrim $ PVInt $ negate x)
    TmPrim (PVReal x) -> return (TmPrim $ PVReal $ negate x)
    TmPrim (PVImaginary x) -> return (TmPrim $ PVImaginary $ negate x)
    TmPrim (PVComplex x) -> return (TmPrim $ PVComplex $ negate x)
    _ -> Left "type error (expected an integer or a real number)"
  BLogicalNot -> (TmPrim . PVBool . not) <$> boolFromValue v
  BNatToInt -> (TmPrim . PVInt) <$> natFromValue v
  BNatToNNReal -> (TmPrim . PVReal . fromIntegral) <$> natFromValue v
  BIntToNat -> (\x -> if x >= 0 then TmPrim (PVInt x) else TmPrim PVZero) <$> intFromValue v
  BIntToReal -> (TmPrim . PVReal . fromIntegral) <$> intFromValue v
  BNNRealToReal -> (TmPrim . PVReal) <$> realFromValue v
  BRealToComplex -> (TmPrim . PVComplex . (:+0)) <$> realFromValue v
  BMkImaginary -> (TmPrim . PVImaginary) <$> realFromValue v
  BImaginaryToComplex -> (TmPrim . PVComplex . (0:+)) <$> imaginaryFromValue v
  BRealPart -> case v of
    TmPrim PVZero -> return v
    TmPrim (PVInt _) -> return v
    TmPrim (PVReal _) -> return v
    TmPrim (PVImaginary _) -> return $ TmPrim PVZero
    TmPrim (PVComplex z) -> return $ TmPrim (PVReal (realPart z))
    _ -> Left "type error (expected a complex number)"
  BImagPart -> case v of
    TmPrim PVZero -> return $ TmPrim PVZero
    TmPrim (PVInt _) -> return $ TmPrim PVZero
    TmPrim (PVReal _) -> return $ TmPrim PVZero
    TmPrim (PVImaginary x) -> return $ TmPrim (PVReal x)
    TmPrim (PVComplex z) -> return $ TmPrim (PVReal (imagPart z))
    _ -> Left "type error (expected a complex number)"
  BAbs -> case v of
    TmPrim PVZero -> return $ TmPrim PVZero
    TmPrim (PVInt x) -> return $ TmPrim (PVInt (abs x))
    TmPrim (PVReal x) -> return $ TmPrim (PVReal (abs x))
    TmPrim (PVImaginary x) -> return $ TmPrim (PVReal (abs x))
    TmPrim (PVComplex z) -> return $ TmPrim (PVReal (magnitude z))
    _ -> Left "type error (expected a complex number)"
  BSqrt -> case v of
    TmPrim PVZero -> return $ TmPrim PVZero
    TmPrim (PVInt x) | x >= 0 -> return $ TmPrim (PVReal (sqrt $ fromIntegral x))
    TmPrim (PVReal x) | x >= 0 -> return $ TmPrim (PVReal (sqrt x))
    TmPrim (PVImaginary x) -> return $ TmPrim (PVComplex (sqrt (0:+x)))
    TmPrim (PVComplex z) -> return $ TmPrim (PVComplex (sqrt z))
    _ -> Left "type error (expected a complex number)"
  _ -> Left "applyBuiltinUnary: not unary"

makeOverloadedFn :: [Either String Term] -> Either String Term
makeOverloadedFn [] = Left "no overload"
makeOverloadedFn [x] = x
makeOverloadedFn (Left _ : xs) = makeOverloadedFn xs
makeOverloadedFn (Right x : xs) = Right x

isZero :: Term -> Bool
isZero (TmPrim PVZero) = True
isZero _ = False

isNonNegative :: Term -> Bool
isNonNegative (TmPrim PVZero) = True
isNonNegative (TmPrim (PVInt x)) = x >= 0
isNonNegative (TmPrim (PVReal x)) = x >= 0
isNonNegative _ = False

applyBuiltinBinary :: Builtin -> Term -> Term -> Either String Term
applyBuiltinBinary f u v = case f of
  BAdd -> makeOverloadedFn [if isZero u && isZero v then return (TmPrim PVZero) else Left "not zero"
                           ,(TmPrim . PVInt) <$> ((+) <$> intFromValue u <*> intFromValue v)
                           ,(TmPrim . PVReal) <$> ((+) <$> realFromValue u <*> realFromValue v)
                           ,(TmPrim . PVImaginary) <$> ((+) <$> imaginaryFromValue u <*> imaginaryFromValue v)
                           ,(TmPrim . PVComplex) <$> ((+) <$> complexFromValue u <*> complexFromValue v)
                           ]
  BSub -> makeOverloadedFn [if isZero u && isZero v then return (TmPrim PVZero) else Left "not zero"
                           ,(TmPrim . PVInt) <$> ((-) <$> intFromValue u <*> intFromValue v)
                           ,(TmPrim . PVReal) <$> ((-) <$> realFromValue u <*> realFromValue v)
                           ,(TmPrim . PVImaginary) <$> ((-) <$> imaginaryFromValue u <*> imaginaryFromValue v)
                           ,(TmPrim . PVComplex) <$> ((-) <$> complexFromValue u <*> complexFromValue v)
                           ]
  BMul -> makeOverloadedFn [if isZero u || isZero v then return (TmPrim PVZero) else Left "not zero"
                           ,(TmPrim . PVInt) <$> ((*) <$> intFromValue u <*> intFromValue v)
                           ,(TmPrim . PVReal) <$> ((*) <$> realFromValue u <*> realFromValue v)
                           ,(TmPrim . PVImaginary) <$> ((*) <$> realFromValue u <*> imaginaryFromValue v)
                           ,(TmPrim . PVImaginary) <$> ((*) <$> imaginaryFromValue u <*> realFromValue v)
                           ,(TmPrim . PVReal . negate) <$> ((*) <$> imaginaryFromValue u <*> imaginaryFromValue v)
                           ,(TmPrim . PVComplex) <$> ((*) <$> complexFromValue u <*> complexFromValue v)
                           ]
  BDiv -> makeOverloadedFn [(TmPrim . PVReal) <$> ((/) <$> realFromValue u <*> realFromValue v)
                           ,(TmPrim . PVImaginary) <$> ((/) <$> imaginaryFromValue u <*> realFromValue v)
                           ,(TmPrim . PVImaginary . negate) <$> ((/) <$> realFromValue u <*> imaginaryFromValue v)
                           ,(TmPrim . PVReal) <$> ((/) <$> imaginaryFromValue u <*> imaginaryFromValue v)
                           ,(TmPrim . PVComplex) <$> ((/) <$> complexFromValue u <*> complexFromValue v)
                           ]
  BPow -> makeOverloadedFn [if isZero v then return (TmPrim (PVInt 1)) else Left "not zero"
                           ,(TmPrim . PVInt) <$> ((^) <$> intFromValue u <*> natFromValue v)
                           ,(TmPrim . PVReal) <$> ((**) <$> nnrealFromValue u <*> realFromValue v)
                           ,(TmPrim . PVReal) <$> ((^^) <$> realFromValue u <*> intFromValue v)
                           ,(TmPrim . PVComplex) <$> ((**) <$> complexFromValue u <*> complexFromValue v)
                           ]
  BTSubNat -> do u' <- natFromValue u
                 v' <- natFromValue v
                 let w | u' >= v' = u' - v'
                       | otherwise = 0
                 return (TmPrim (PVInt w))
  BLt -> (TmPrim . PVBool) <$> ((<) <$> realFromValue u <*> realFromValue v)
  BLe -> (TmPrim . PVBool) <$> ((<=) <$> realFromValue u <*> realFromValue v)
  BEqual -> (TmPrim . PVBool) <$> ((==) <$> complexFromValue u <*> complexFromValue v)
  BMax -> makeOverloadedFn [(TmPrim . PVInt) <$> (max <$> intFromValue u <*> intFromValue v)
                           ,(TmPrim . PVReal) <$> (max <$> realFromValue u <*> realFromValue v)
                           ]
  BMin -> makeOverloadedFn [if (isZero u && isNonNegative v) || (isZero v && isNonNegative u) then return (TmPrim PVZero) else Left "not zero"
                           ,(TmPrim . PVInt) <$> (min <$> intFromValue u <*> intFromValue v)
                           ,(TmPrim . PVReal) <$> (min <$> realFromValue u <*> realFromValue v)
                           ]
  BIntDiv -> (TmPrim . PVInt) <$> (div <$> intFromValue u <*> intFromValue v)
  BIntMod -> (TmPrim . PVInt) <$> (mod <$> intFromValue u <*> intFromValue v)
  BGcd -> (TmPrim . PVInt) <$> (gcd <$> intFromValue u <*> intFromValue v)
  BLcm -> (TmPrim . PVInt) <$> (lcm <$> intFromValue u <*> intFromValue v)
  BLogicalAnd -> (TmPrim . PVBool) <$> ((&&) <$> boolFromValue u <*> boolFromValue v)
  BLogicalOr -> (TmPrim . PVBool) <$> ((||) <$> boolFromValue u <*> boolFromValue v)
  _ -> Left "not implemented yet; sorry"

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
        TmPrim (PVBuiltin f) | isUnary f -> applyBuiltinUnary f v
        TmPrim (PVBuiltin _) -> return t -- partial application
        TmApp (TmPrim (PVBuiltin f)) u' | isBinary f -> applyBuiltinBinary f u' v
        TmApp (TmApp (TmTyApp (TmPrim (PVBuiltin BIterate)) ty) n) z -> do
          n' <- natFromValue n
          if n' == 0
            then return $ z
            else return $ TmApp (TmApp (TmApp (TmTyApp (TmPrim (PVBuiltin BIterate)) ty) (TmPrim (PVInt (n' - 1)))) (TmApp v z)) v
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
