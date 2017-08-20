{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE BangPatterns #-}
module Polestar.Type where
import Data.Complex
import Data.Monoid
import Data.Ord

-- variable name (for debugging)
newtype Id = Id String deriving (Show)

-- ordering: s <: t implies s < t
data PrimType
  -- numeric types
  = PTyZero
  | PTyNat
  | PTyInt
  | PTyNNReal -- non-negative real number
  | PTyReal
  | PTyImaginary
  | PTyComplex
  -- boolean
  | PTyTrue
  | PTyFalse
  | PTyBool
  -- other
  | PTyUnit
  deriving (Eq,Ord,Show,Enum,Bounded)

data Type = TyPrim !PrimType
          | TyArr Type Type
          | TyAll Id !(Maybe Type) Type
          | TyRef !Int
          | TyTuple [Type] -- must have 2 or more elements
          | TyInter [Type] -- must have 2 or more elements
          deriving (Eq,Show)

pattern TyZero = TyPrim PTyZero
pattern TyNat = TyPrim PTyNat
pattern TyInt = TyPrim PTyInt
pattern TyNNReal = TyPrim PTyNNReal
pattern TyReal = TyPrim PTyReal
pattern TyImaginary = TyPrim PTyImaginary
pattern TyComplex = TyPrim PTyComplex
pattern TyTrue = TyPrim PTyTrue
pattern TyFalse = TyPrim PTyFalse
pattern TyBool = TyPrim PTyBool
pattern TyUnit = TyPrim PTyUnit
pattern TyPair a b = TyTuple [a,b]

-- compound canonical type
-- no pair of the components have subtyping relation
type CanonicalType = [ICanonicalType]

-- individual canonical type
data ICanonicalType = CTyPrim !PrimType
                    | CTyArr CanonicalType ICanonicalType
                    | CTyAll Id CanonicalType ICanonicalType
                    | CTyRef !Int
                    | CTyTuple [ICanonicalType]
                    deriving (Eq,Show)

pattern CTyTrue = CTyPrim PTyTrue
pattern CTyFalse = CTyPrim PTyFalse
pattern CTyBool = CTyPrim PTyBool

data Builtin
  -- unary
  = BNegate
  | BLogicalNot
  | BNatToInt
  | BNatToNNReal
  | BIntToNat -- max(n,0)
  | BIntToReal
  | BNNRealToReal
  | BRealToComplex
  | BMkImaginary
  | BImaginaryToComplex
  | BRealPart
  | BImagPart
  | BAbs
  | BSqrt
  -- binary
  | BAdd
  | BSub
  | BMul
  | BDiv
  | BPow
  | BTSubNat -- truncated subtraction
  | BLt
  | BLe
  | BEqual
  | BMax
  | BMin
  | BLogicalAnd
  | BLogicalOr
  -- | BIterate
  -- | BUnsafeGlue
  deriving (Eq,Show,Enum,Bounded)

data PrimValue = PVZero
               | PVInt !Integer
               | PVReal !Double
               | PVImaginary !Double
               | PVComplex !(Complex Double)
               | PVBool !Bool
               | PVUnit
               | PVBuiltin !Builtin
               -- 'iterate' function
               deriving (Eq,Show)

data Term = TmPrim !PrimValue             -- primitive value
          | TmAbs Id Type Term            -- lambda abstraction
          | TmTyAbs Id !(Maybe Type) Term -- bounded type abstraction
          | TmRef !Int                    -- variable (de Bruijn index)
          | TmApp Term Term               -- function application
          | TmTyApp Term Type             -- type application
          | TmLet Id Term Term            -- let-in
          | TmAlt Id [Type] Term          -- type alternation
          | TmIf Term Term Term           -- if-then-else
          | TmTuple [Term]                -- tuple
          | TmProj Term !Int              -- projection
          | TmCoerce Term Type            -- coercion
          | TmCoherentTuple [Term]        -- coherent tuple
          deriving (Eq,Show)

data Binding = VarBind Id CanonicalType
             | TyVarBind Id CanonicalType
             | AnonymousBind
             deriving (Eq,Show)

arity :: Builtin -> Int
arity f = case f of
  BNegate -> 1
  BIntToReal -> 1
  BNatToInt -> 1
  BIntToNat -> 1
  _ -> 2

isValue :: Term -> Bool
isValue t = case t of
  TmPrim _ -> True
  TmAbs _ _ _ -> True
  TmTyAbs _ _ _ -> True
  TmApp (TmPrim (PVBuiltin f)) x | arity f > 1 -> isValue x -- partial application
  TmTuple xs -> all isValue xs
  TmCoherentTuple xs -> all isValue xs
  _ -> False

getCTypeFromContext :: [Binding] -> Int -> CanonicalType
getCTypeFromContext ctx i
  | 0 <= i && i < length ctx = case ctx !! i of
      VarBind _ ty -> ty
      b -> error ("TmRef: expected a variable binding, found " ++ show b)
  | otherwise = error "TmRef: index out of bounds"

getTypeFromContext :: [Binding] -> Int -> Type
getTypeFromContext ctx i = canonicalToOrdinary $ getCTypeFromContext ctx i

getCBoundFromContext :: [Binding] -> Int -> CanonicalType
getCBoundFromContext ctx i
  | i < length ctx = case ctx !! i of
                       TyVarBind _ b -> b
                       b -> error ("TyRef: expected a type variable binding, found " ++ show b)
  | otherwise = error "TyRef: index out of bounds"

getBoundFromContext :: [Binding] -> Int -> Maybe Type
getBoundFromContext ctx i = canonicalToOrdinaryM $ getCBoundFromContext ctx i

typeShift :: Int -> Int -> Type -> Type
-- typeShift 0 _ ty = ty
typeShift !delta = go
  where
    go !i ty = case ty of
      TyPrim _ -> ty
      TyArr u v -> TyArr (go i u) (go (i + 1) v)
      TyAll name b t -> TyAll name (typeShift delta i <$> b) (typeShift delta (i + 1) t)
      TyRef j | j >= i, j + delta >= 0 -> TyRef (j + delta)
              | j >= i, j + delta < 0 -> error "typeShift: negative index"
              | otherwise -> ty
      TyTuple tys -> TyTuple $ map (go i) tys
      TyInter tys -> TyInter $ map (go i) tys

typeShiftC :: Int -> Int -> CanonicalType -> CanonicalType
-- typeShiftC 0 _ = id
typeShiftC !delta !i = map (typeShiftI delta i)

typeShiftI :: Int -> Int -> ICanonicalType -> ICanonicalType
typeShiftI !delta = go
  where
    go :: Int -> ICanonicalType -> ICanonicalType
    go !i ty = case ty of
      CTyPrim _ -> ty
      CTyArr u v -> CTyArr (map (go i) u) (go (i + 1) v)
      CTyAll name b t -> CTyAll name (map (go i) b) (go (i + 1) t)
      CTyRef j | j >= i, j + delta >= 0 -> CTyRef (j + delta)
               | j >= i, j + delta < 0 -> error "typeShift: negative index"
               | otherwise -> ty
      CTyTuple tys -> CTyTuple $ map (go i) tys

typeSubstD :: Int -> Type -> Int -> Type -> Type
typeSubstD !depth s !i ty = case ty of
  TyPrim _ -> ty
  TyArr u v -> TyArr (typeSubstD depth s i u) (typeSubstD (depth + 1) s (i + 1) v)
  TyAll name b t -> TyAll name (typeSubstD depth s i <$> b) (typeSubstD (depth + 1) s (i + 1) t)
  TyRef j | j == i -> typeShift depth 0 s
          | j > i -> TyRef (j - 1)
          | otherwise -> ty
  TyTuple tys -> TyTuple $ map (typeSubstD depth s i) tys
  TyInter tys -> TyInter $ map (typeSubstD depth s i) tys

typeSubst = typeSubstD 0

typeSubstCD :: Int -> CanonicalType -> Int -> ICanonicalType -> CanonicalType
typeSubstCD !depth s !i ty = case ty of
  CTyPrim _ -> return ty
  CTyArr u v -> CTyArr (u >>= typeSubstCD depth s i) <$> typeSubstCD (depth + 1) s (i + 1) v
  CTyAll name b t -> CTyAll name (b >>= typeSubstCD depth s i) <$> typeSubstCD (depth + 1) s (i + 1) t
  CTyRef j | j == i -> typeShiftC depth 0 s
           | j > i -> return $ CTyRef (j - 1)
           | otherwise -> return ty
  CTyTuple tys -> CTyTuple <$> mapM (typeSubstCD depth s i) tys

typeSubstC = typeSubstCD 0

canonicalToOrdinary :: CanonicalType -> Type
canonicalToOrdinary [] = error "canonicalToOrdinary: Top type"
canonicalToOrdinary [t] = iCanonicalToOrdinary t
canonicalToOrdinary tys = TyInter $ map iCanonicalToOrdinary tys

canonicalToOrdinaryM :: CanonicalType -> Maybe Type
canonicalToOrdinaryM [] = Nothing
canonicalToOrdinaryM [t] = Just $ iCanonicalToOrdinary t
canonicalToOrdinaryM tys = Just $ TyInter $ map iCanonicalToOrdinary tys

iCanonicalToOrdinary :: ICanonicalType -> Type
iCanonicalToOrdinary (CTyPrim p) = TyPrim p
iCanonicalToOrdinary (CTyArr u v) = TyArr (canonicalToOrdinary u) (iCanonicalToOrdinary v)
iCanonicalToOrdinary (CTyAll name b t) = TyAll name (canonicalToOrdinaryM b) (iCanonicalToOrdinary t)
iCanonicalToOrdinary (CTyRef i) = TyRef i
iCanonicalToOrdinary (CTyTuple tys) = TyTuple $ map iCanonicalToOrdinary tys


instance Eq Id where
  _ == _ = True

{-
instance Ord ICanonicalType where
  compare (CTyPrim p) (CTyPrim p') = compare p p'
  compare (CTyArr s t) (CTyArr s' t') = compare (Down s) (Down s') <> compare t t'
  compare (CTyAll _ s t) (CTyAll _ s' t') = compare (Down s) (Down s') <> compare t t'
  compare (CTyRef i) (CTyRef i') = compare i i'
  compare (CTyTuple tys) (CTyTuple tys') = compare tys tys'
  compare (CTyPrim _) _ = LT
  compare _ (CTyPrim _) = GT
  compare (CTyArr _ _) _ = LT
  compare _ (CTyArr _ _) = GT
  compare (CTyAll _ _ _) _ = LT
  compare _ (CTyAll _ _ _) = GT
  compare (CTyRef _) _ = LT
  compare _ (CTyRef _) = GT
  -- compare (CTyTuple _) _ = LT
  -- compare _ (CTyTuple _) = GT
-}
