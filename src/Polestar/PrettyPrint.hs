module Polestar.PrettyPrint
  (prettyPrintTypeP
  ,prettyPrintType
  ,prettyPrintCanonicalTypeP
  ,prettyPrintICanonicalTypeP
  ,prettyPrintTermP
  ,prettyPrintTerm
  ) where
import Polestar.Type
import Polestar.Parse (NameBinding(..))
import Data.List (intersperse)
import Data.Complex

varNames :: [NameBinding] -> [String]
varNames = foldr (\x ys -> case x of
                             NVarBind n -> n:ys
                             _ -> ys) []

tyVarNames :: [NameBinding] -> [String]
tyVarNames = foldr (\x ys -> case x of
                               NTyVarBind n -> n:ys
                               _ -> ys) []

rename :: [String] -> String -> String
rename ctx name | name `notElem` ctx = name
                | otherwise = loop 1
  where loop :: Int -> String
        loop i = case name ++ show i of
          m | m `notElem` ctx -> m
          _ -> loop (i + 1)

showPrimType :: PrimType -> ShowS
showPrimType p = case p of
  PTyZero -> showString "Zero"
  PTyNat -> showString "Nat"
  PTyInt -> showString "Int"
  PTyNNReal -> showString "NNReal"
  PTyReal -> showString "Real"
  PTyImaginary -> showString "Imaginary"
  PTyComplex -> showString "Complex"
  PTyTrue -> showString "True"
  PTyFalse -> showString "False"
  PTyBool -> showString "Bool"
  PTyUnit -> showString "Unit"

-- <3>: <primitive type> | <type variable> | <0>
-- <2>: <3> -> <2>
-- <1>: <2> & .. & <2>
-- <0>: forall a <: <1>. <0> | <1>
prettyPrintTypeP :: Int -> [NameBinding] -> Type -> ShowS
prettyPrintTypeP p ctx t = case t of
  TyPrim p -> showPrimType p
  TyArr s t -> showParen (p > 2) $ prettyPrintTypeP 3 ctx s . showString " -> " . prettyPrintTypeP 2 (NAnonymousBind : ctx) t
  TyRef i | i < length ctx -> case ctx !! i of
              NTyVarBind n -> showString n
              n -> showString "<invalid type variable reference #" . shows i . showString ": " . shows n . showChar '>'
          | otherwise -> showString "<invalid type variable reference #" . shows i . showString ", index out of range>"
  TyAll (Id name) Nothing t -> showParen (p > 0) $ showString "forall " . showString name' . showString ". " . prettyPrintTypeP 0 (NTyVarBind name' : ctx) t
    where name' = rename (tyVarNames ctx) name
  TyAll (Id name) (Just b) t -> showParen (p > 0) $ showString "forall " . showString name' . showString "<:" . prettyPrintTypeP 1 ctx b . showString ". " . prettyPrintTypeP 0 (NTyVarBind name' : ctx) t
    where name' = rename (tyVarNames ctx) name
  TyInter tys -> showParen (p > 1) $ foldr (.) id $ intersperse (showString " & ") $ map (prettyPrintTypeP 2 ctx) tys
  TyTuple components -> showParen True $ foldr (.) id $ intersperse (showString ", ") $ map (prettyPrintTypeP 0 ctx) components

prettyPrintType :: Type -> String
prettyPrintType t = prettyPrintTypeP 0 [] t ""

prettyPrintCanonicalTypeP :: Int -> [NameBinding] -> CanonicalType -> ShowS
prettyPrintCanonicalTypeP p ctx [] = showString "<untyped>"
prettyPrintCanonicalTypeP p ctx [t] = prettyPrintICanonicalTypeP p ctx t
prettyPrintCanonicalTypeP p ctx ts = showParen (p > 1) $ foldl1 (\x y -> x . showString " & " . y) $ map (prettyPrintICanonicalTypeP 2 ctx) ts

prettyPrintICanonicalTypeP :: Int -> [NameBinding] -> ICanonicalType -> ShowS
prettyPrintICanonicalTypeP p ctx t = case t of
  CTyPrim p -> showPrimType p
  CTyArr s t -> showParen (p > 2) $ prettyPrintCanonicalTypeP 3 ctx s . showString " -> " . prettyPrintICanonicalTypeP 2 (NAnonymousBind : ctx) t
  CTyRef i | i < length ctx -> case ctx !! i of
               NTyVarBind n -> showString n
               n -> showString "<invalid type variable reference #" . shows i . showString ": " . shows n . showChar '>'
           | otherwise -> showString "<invalid type variable reference #" . shows i . showString ", index out of range>"
  CTyAll (Id name) [] t -> showParen (p > 0) $ showString "forall " . showString name' . showString ". " . prettyPrintICanonicalTypeP 0 (NTyVarBind name' : ctx) t
    where name' = rename (tyVarNames ctx) name
  CTyAll (Id name) b t -> showParen (p > 0) $ showString "forall " . showString name' . showString "<:" . prettyPrintCanonicalTypeP 1 ctx b . showString ". " . prettyPrintICanonicalTypeP 0 (NTyVarBind name' : ctx) t
    where name' = rename (tyVarNames ctx) name
  CTyTuple components -> showParen True $ foldr (.) id $ intersperse (showString ", ") $ map (prettyPrintICanonicalTypeP 0 ctx) components

-- <2>: <primitive> | <variable> | (<0>)
-- <1>: <1> <2> | <1> [ty] | <1> as <type>
-- <0>: \x:t. <0> | ?a. <0> | if <0> then <0> else <0>
prettyPrintTermP :: Int -> [NameBinding] -> Term -> ShowS
prettyPrintTermP p ctx t = case t of
  TmPrim (PVZero) -> showChar '0'
  TmPrim (PVInt x) -> shows x
  TmPrim (PVReal x) -> shows x
  TmPrim (PVImaginary x) -> shows x . showChar 'i'
  TmPrim (PVComplex (x :+ y)) -> showParen True $ shows x . showChar '+' . shows y . showChar 'i'
  TmPrim (PVBool x) -> if x then showString "true" else showString "false"
  TmPrim PVUnit -> showString "unit"
  TmPrim (PVBuiltin f) -> showString $ case f of
    BNegate -> "negate"
    BLogicalNot -> "not"
    BNatToInt -> "natToInt"
    BNatToNNReal -> "natToNNReal"
    BIntToNat -> "intToNat"
    BIntToReal -> "intToReal"
    BNNRealToReal -> "nnrealToReal"
    BRealToComplex -> "realToComplex"
    BMkImaginary -> "mkImaginary"
    BImaginaryToComplex -> "imaginaryToComplex"
    BRealPart -> "realPart"
    BImagPart -> "imagPart"
    BAbs -> "abs"
    BSqrt -> "sqrt"
    BAdd -> "add"
    BSub -> "sub"
    BMul -> "mul"
    BDiv -> "div"
    BPow -> "pow"
    BTSubNat -> "tSub"
    BLt -> "lt"
    BLe -> "le"
    BEqual -> "equal"
    BMax -> "max"
    BMin -> "min"
    BIntDiv -> "intDiv"
    BIntMod -> "mod"
    BGcd -> "gcd"
    BLcm -> "lcm"
    BLogicalAnd -> "and"
    BLogicalOr -> "or"
    BIterate -> "iterate"
  TmAbs (Id name) ty body -> showParen (p > 0) $ showChar '\\' . showString name' . showChar ':' . prettyPrintTypeP 1 ctx ty . showString ". " . prettyPrintTermP 0 (NVarBind name' : ctx) body
    where name' = rename (varNames ctx) name
  TmTyAbs (Id name) Nothing body -> showParen (p > 0) $ showString "?" . showString name' . showString ". " . prettyPrintTermP 0 (NTyVarBind name' : ctx) body
    where name' = rename (tyVarNames ctx) name
  TmTyAbs (Id name) (Just b) body -> showParen (p > 0) $ showString "?" . showString name' . showString "<:" . prettyPrintTypeP 1 ctx b . showString ". " . prettyPrintTermP 0 (NTyVarBind name' : ctx) body
    where name' = rename (tyVarNames ctx) name
  TmRef i | i < length ctx -> case ctx !! i of
              NVarBind n -> showString n
              n -> showString "<invalid variable reference #" . shows i . showString ": " . shows n . showChar '>'
          | otherwise -> showString "<invalid variable reference #" . shows i . showString ", index out of range>"
  TmApp u v -> showParen (p > 1) $ prettyPrintTermP 1 ctx u . showChar ' ' . prettyPrintTermP 2 ctx v
  TmTyApp u t -> showParen (p > 1) $ prettyPrintTermP 1 ctx u . showString " [" . prettyPrintTypeP 0 ctx t . showChar ']'
  TmLet (Id name) def body -> showParen (p > 0) $ showString "let " . showString name' . showString " = " . prettyPrintTermP 0 ctx def . showString " in " . prettyPrintTermP 0 (NVarBind name' : ctx) body
    where name' = rename (varNames ctx) name
  TmIf cond then_ else_ -> showParen (p > 0) $ showString "if " . prettyPrintTermP 0 ctx cond . showString " then " . prettyPrintTermP 0 ctx then_ . showString " else " . prettyPrintTermP 0 ctx else_
  TmCoerce x t -> showParen (p > 1) $ prettyPrintTermP 1 ctx x . showString " as " . prettyPrintTypeP 1 ctx t
  TmAlt (Id name) candidates body -> showParen (p > 0) $ showString "for " . showString name' . showString " in " . foldr (.) id (intersperse (showString ", ") $ map (prettyPrintTypeP 1 ctx) candidates) . showString ". " . prettyPrintTermP 0 (NTyVarBind name' : ctx) body
    where name' = rename (tyVarNames ctx) name
  TmTuple components -> showParen True $ foldr (.) id $ intersperse (showString ", ") $ map (prettyPrintTermP 0 ctx) components
  TmProj tuple i -> showParen (p > 1) $ prettyPrintTermP 1 ctx tuple . showString " @" . shows i
  TmCoherentTuple components -> showString "<coherent tuple: " . (foldr (.) id $ intersperse (showString ", ") $ map (prettyPrintTermP 0 ctx) components) . showString ">"

prettyPrintTerm :: Term -> String
prettyPrintTerm t = prettyPrintTermP 0 [] t ""
