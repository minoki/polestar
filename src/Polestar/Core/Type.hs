{-# LANGUAGE PatternSynonyms #-}
module Polestar.Core.Type where

data PrimType = PTyNat
              | PTyInt
              | PTyReal
              | PTyBool
              | PTyUnit
              deriving (Eq,Show,Enum,Bounded)

data Type = TyPrim !PrimType
          | TyArr Type Type
          | TyTuple [Type] -- must have 2 or more elements
          deriving (Eq,Show)

pattern TyNat = TyPrim PTyNat
pattern TyInt = TyPrim PTyInt
pattern TyReal = TyPrim PTyReal
pattern TyBool = TyPrim PTyBool
pattern TyUnit = TyPrim PTyUnit
pattern TyPair a b = TyTuple [a,b]

newtype Id = Id String deriving (Show)

data UnaryFn = UNegateInt
             | UNegateReal
             | UNatToInt
             | UIntToReal
             | UIntToNat -- max(n,0)
             deriving (Eq,Show,Enum,Bounded)

data BinaryFn

  -- Natural number
  = UAddNat
  | UMulNat
  | UTSubNat -- truncated subtraction
  | UPowNatNat
  | UEqualNat
  | ULessThanNat
  | ULessEqualNat

  -- Integer
  | UAddInt
  | USubInt
  | UMulInt
  | UPowIntNat
  | UEqualInt
  | ULessThanInt
  | ULessEqualInt

  -- Real numbers
  | UAddReal
  | USubReal
  | UMulReal
  | UDivReal
  | UPowRealReal
  | UEqualReal
  | ULessThanReal
  | ULessEqualReal

  deriving (Eq,Show,Enum,Bounded)

data PrimValue = PVNat !Integer
               | PVInt !Integer
               | PVReal !Double
               | PVBool !Bool
               | PVUnit
               | PVUnary !UnaryFn
               | PVBinary !BinaryFn
               deriving (Eq,Show)

data Term = TmPrim !PrimValue
          | TmAbs Id Type Term
          | TmRef !Int
          | TmApp Term Term
          | TmLet Id Term Term
          | TmIf Term Term Term
          | TmTuple [Term]
          | TmProj Term !Int
          | TmIterate Term Term Term
          deriving (Eq,Show)

data Binding = VarBind Id Type
             | AnonymousBind
             deriving (Eq,Show)

isValue :: Term -> Bool
isValue t = case t of
  TmPrim _ -> True
  TmAbs _ _ _ -> True
  TmApp (TmPrim (PVBinary _)) x -> isValue x -- partial application
  TmTuple components -> all isValue components
  _ -> False

getTypeFromContext :: [Binding] -> Int -> Type
getTypeFromContext ctx i
  | 0 <= i && i < length ctx = case ctx !! i of
      VarBind _ ty -> ty
      b -> error ("TmRef: expected a variable binding, found " ++ show b)
  | otherwise = error "TmRef: index out of bounds"

typeSubstD :: Int -> Type -> Int -> Type -> Type
typeSubstD _ _ _ = id

typeShift :: Int -> Int -> Type -> Type
typeShift _ _ = id

isScalarType :: Type -> Bool
isScalarType (TyPrim _) = True
isScalarType (TyArr _ _) = False
isScalarType (TyTuple components) = all isScalarType components

instance Eq Id where
  _ == _ = True
