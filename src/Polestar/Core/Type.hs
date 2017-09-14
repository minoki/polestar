{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}
module Polestar.Core.Type where
import GHC.Generics (Generic)
import Control.DeepSeq

data PrimType = PTyNat
              | PTyInt
              | PTyReal
              | PTyBool
              | PTyUnit
              deriving (Eq,Show,Enum,Bounded,Generic,NFData)

data Type = TyPrim !PrimType
          | TyArr Type Type
          | TyTuple [Type] -- must have 2 or more elements
          deriving (Eq,Show,Generic,NFData)

pattern TyNat = TyPrim PTyNat
pattern TyInt = TyPrim PTyInt
pattern TyReal = TyPrim PTyReal
pattern TyBool = TyPrim PTyBool
pattern TyUnit = TyPrim PTyUnit
pattern TyPair a b = TyTuple [a,b]

newtype Id = Id String deriving (Show,Generic,NFData)

data UnaryFn = UNegateInt
             | UNegateReal
             | UNatToInt
             | UIntToReal
             | UIntToNat -- max(n,0)
             deriving (Eq,Show,Enum,Bounded,Generic,NFData)

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

  deriving (Eq,Show,Enum,Bounded,Generic,NFData)

data PrimValue = PVNat !Integer
               | PVInt !Integer
               | PVReal !Double
               | PVBool !Bool
               | PVUnit
               | PVUnary !UnaryFn
               | PVBinary !BinaryFn
               deriving (Eq,Show,Generic,NFData)

data Term = TmPrim !PrimValue
          | TmAbs Id Type Term
          | TmRef !Int
          | TmApp Term Term
          | TmLet Id Term Term
          | TmTypedLet Id Type Term Term
          | TmIf Term Term Term
          | TmTuple [Term]
          | TmProj Term !Int
          | TmIterate Term Term Term
          deriving (Eq,Show,Generic,NFData)

pattern TmUnary f u = TmApp (TmPrim (PVUnary f)) u
pattern TmBinary f u v = TmApp (TmApp (TmPrim (PVBinary f)) u) v
pattern TmBinaryPA f u = TmApp (TmPrim (PVBinary f)) u -- partial application

data Binding = VarBind Id Type
             | AnonymousBind
             deriving (Eq,Show,Generic,NFData)

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
