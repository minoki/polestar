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
             | UIntToReal
             | UNatToInt
             | UIntToNat -- max(n,0)
             deriving (Eq,Show,Enum,Bounded)

data BinaryFn = UAddNat
              | UMulNat
              | UTSubNat -- truncated subtraction
              | UAddInt
              | USubInt
              | UMulInt
              | UAddReal
              | USubReal
              | UMulReal
              | UDivReal
              | ULtReal
              | ULeReal
              | UEqualReal
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
          | TmProj Term !Int
          deriving (Eq,Show)

data Binding = VarBind Id Type
             | AnonymousBind
             deriving (Eq,Show)

isValue :: Term -> Bool
isValue t = case t of
  TmPrim _ -> True
  TmAbs _ _ _ -> True
  TmApp (TmPrim (PVBinary _)) x -> isValue x -- partial application
  _ -> False

getTypeFromContext :: [Binding] -> Int -> Type
getTypeFromContext ctx i
  | 0 <= i && i < length ctx = case ctx !! i of
      VarBind _ ty -> ty
      b -> error ("TmRef: expected a variable binding, found " ++ show b)
  | otherwise = error "TmRef: index out of bounds"

instance Eq Id where
  _ == _ = True
