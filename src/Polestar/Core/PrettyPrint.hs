module Polestar.Core.PrettyPrint
  (prettyPrintTypeP
  ,prettyPrintType
  ,prettyPrintTermP
  ,prettyPrintTerm
  ) where
import Polestar.Core.Type
import Polestar.Core.Parse (NameBinding(..),unaryFns,binaryFns)
import Data.List (find,intersperse)
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
  PTyNat -> showString "Nat"
  PTyInt -> showString "Int"
  PTyReal -> showString "Real"
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
  TyTuple components -> showParen True $ foldr (.) id $ intersperse (showString ", ") $ map (prettyPrintTypeP 0 ctx) components

prettyPrintType :: Type -> String
prettyPrintType t = prettyPrintTypeP 0 [] t ""

unaryFnName :: UnaryFn -> String
unaryFnName f | Just (name,_) <- find ((== f) . snd) unaryFns = name
              | otherwise = "<name not found: " ++ show f ++ ">"

binaryFnName :: BinaryFn -> String
binaryFnName f | Just (name,_) <- find ((== f) . snd) binaryFns = name
               | otherwise = "<name not found: " ++ show f ++ ">"

-- <2>: <primitive> | <variable> | (<0>)
-- <1>: <1> <2> | <1> [ty] | <1> as <type>
-- <0>: \x:t. <0> | ?a. <0> | if <0> then <0> else <0>
prettyPrintTermP :: Int -> [NameBinding] -> Term -> ShowS
prettyPrintTermP p ctx t = case t of
  TmPrim (PVNat x) -> shows x
  TmPrim (PVInt x) -> shows x
  TmPrim (PVReal x) -> shows x
  TmPrim (PVBool x) -> if x then showString "true" else showString "false"
  TmPrim PVUnit -> showString "unit"
  TmPrim (PVUnary f) -> showString (unaryFnName f)
  TmPrim (PVBinary f) -> showString (binaryFnName f)
  TmAbs (Id name) ty body -> showParen (p > 0) $ showChar '\\' . showString name' . showChar ':' . prettyPrintTypeP 1 ctx ty . showString ". " . prettyPrintTermP 0 (NVarBind name' : ctx) body
    where name' = rename (varNames ctx) name
  TmRef i | i < length ctx -> case ctx !! i of
              NVarBind n -> showString n
              n -> showString "<invalid variable reference #" . shows i . showString ": " . shows n . showChar '>'
          | otherwise -> showString "<invalid variable reference #" . shows i . showString ", index out of range>"
  TmApp u v -> showParen (p > 1) $ prettyPrintTermP 1 ctx u . showChar ' ' . prettyPrintTermP 2 ctx v
  TmLet (Id name) def body -> showParen (p > 0) $ showString "let " . showString name' . showString " = " . prettyPrintTermP 0 ctx def . showString " in " . prettyPrintTermP 0 (NVarBind name' : ctx) body
    where name' = rename (varNames ctx) name
  TmIf cond then_ else_ -> showParen (p > 0) $ showString "if " . prettyPrintTermP 0 ctx cond . showString " then " . prettyPrintTermP 0 ctx then_ . showString " else " . prettyPrintTermP 0 ctx else_
  TmTuple components -> showParen True $ foldr (.) id $ intersperse (showString ", ") $ map (prettyPrintTermP 0 ctx) components
  TmProj tuple i -> showParen (p > 1) $ prettyPrintTermP 1 ctx tuple . showString " @" . shows i
  TmIterate n init succ -> showParen (p > 1) $ showString "iterate " . prettyPrintTermP 2 ctx n . showChar ' ' . prettyPrintTermP 2 ctx init . showChar ' ' . prettyPrintTermP 2 ctx succ

prettyPrintTerm :: Term -> String
prettyPrintTerm t = prettyPrintTermP 0 [] t ""
