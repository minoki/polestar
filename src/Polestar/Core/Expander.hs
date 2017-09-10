module Polestar.Core.Expander where
import Polestar.Core.Type
import Polestar.Core.TypeCheck
import Polestar.Core.Eval
import Control.Arrow
import Control.Monad.Except

data EBinding = EVarBind Id Type
              | ELetBind Id Type Term
              deriving (Eq,Show)

isSimple :: Term -> Bool
isSimple t = case t of
  TmPrim _ -> True
  TmRef _ -> True
  _ -> False

doApply :: [EBinding] -> Term -> Term -> Either String Term
doApply ctx f x = case f of
  TmPrim (PVUnary f) -> pure (TmUnary f x)
  TmPrim (PVBinary f) -> pure (TmBinaryPA f x)
  TmBinaryPA f u -> pure (TmBinary f u x)
  TmAbs name ty@(TyArr _ _) body -> snd <$> expand ctx (termSubst x 0 body)
  TmAbs name ty body | isSimple x -> pure (termSubst x 0 body)
                     | otherwise -> pure (TmTypedLet name ty x body)
  -- TmLet name def body -> TmLet name def <$> doApply (ELetBind name {- -} def : ctx) body (termShift 1 0 x)
  TmTypedLet name ty def body -> TmTypedLet name ty def <$> doApply (ELetBind name ty def : ctx) body (termShift 1 0 x)
  TmRef i | i < length ctx, ELetBind _ _ def <- ctx !! i -> doApply ctx (termShift (i + 1) 0 def) x
          | otherwise -> pure (TmApp f x)
  _ -> throwError "doApply: this form is not supported"

doIfThenElse :: [EBinding] -> Type -> Term -> Term -> Term -> Either String Term
doIfThenElse ctx (TyArr argType retType) cond then_ else_ = do
  let ctx' = EVarBind (Id "_") argType : ctx
  then' <- doApply ctx' (termShift 1 0 then_) (TmRef 0)
  else' <- doApply ctx' (termShift 1 0 else_) (TmRef 0)
  body <- doIfThenElse ctx' retType (termShift 1 0 cond) then' else'
  pure (TmAbs (Id "_") argType body)
doIfThenElse _ ty cond then_ else_ = pure (TmIf cond then_ else_)

expand :: [EBinding] -> Term -> Either String (Type,Term)
expand ctx t = case t of
  TmPrim p -> pure (primTypeOf p, t)
  TmAbs name ty body -> do
    (bodyType,body') <- expand (EVarBind name ty : ctx) body
    pure (TyArr ty bodyType, TmAbs name ty body')
  TmRef i | i < length ctx -> case ctx !! i of
              EVarBind _ ty -> pure (ty, t)
              ELetBind _ ty@(TyArr _ _) f -> pure (ty, termShift (i + 1) 0 f)
              ELetBind _ ty x | isSimple x -> pure (ty, termShift (i + 1) 0 x)
              ELetBind _ ty _ -> pure (ty, t) -- TODO: tuple?
          | otherwise -> throwError "invalid variable referenece"
  TmApp f x -> do
    (fnType, f') <- expand ctx f
    (actualArgType, x') <- expand ctx x
    case fnType of
      TyArr expectedArgType retType
        | expectedArgType == actualArgType -> (,) retType <$> doApply ctx f' x'
        | otherwise -> throwError ("type error (expected: " ++ show expectedArgType ++ ", got: " ++ show actualArgType ++ ")")
      _ -> throwError ("invalid function application (expected function type, got: " ++ show fnType ++ ")")
  TmLet name def body -> do
    (definedType,def') <- expand ctx def
    (bodyType,body') <- expand (ELetBind name definedType def' : ctx) body
    return (bodyType, TmTypedLet name definedType def' body')
  TmTypedLet name ty def body -> do
    (definedType,def') <- expand ctx def
    guardWithMessage (ty == definedType) "typed let: declared type must match with the actual type"
    (bodyType,body') <- expand (ELetBind name definedType def' : ctx) body
    return (bodyType, TmTypedLet name ty def' body')
  TmIf cond then_ else_ -> do
    (condType, cond') <- expand ctx cond
    guardWithMessage (condType == TyBool) "if-then-else: condition must be boolean"
    (thenType, then') <- expand ctx then_
    (elseType, else') <- expand ctx else_
    guardWithMessage (thenType == elseType) "if-then-else: incompatible types"
    (,) thenType <$> doIfThenElse ctx thenType cond' then' else'
  TmTuple components -> do
    components' <- mapM (expand ctx) components
    return (TyTuple $ map fst components', TmTuple $ map snd components')
  TmProj tuple i -> do
    (tupleTy, tuple') <- expand ctx tuple
    case tupleTy of
      TyTuple types | i < length types -> pure (types !! i, TmProj tuple' i)
                    | otherwise -> throwError "the size of the tuple must be larger than index"
      _ -> throwError "expression must be a tuple"
  TmIterate n init succ -> do
    (nTy,n') <- expand ctx n
    guardWithMessage (nTy == TyNat) "iterate: count must be a natural number"
    (initTy,init') <- expand ctx init
    (succTy,succ') <- expand ctx succ
    let expectedSuccTy = TyArr initTy (typeShift 1 0 initTy)
    guardWithMessage (succTy == expectedSuccTy) ("iterate: succ function must be " ++ show expectedSuccTy)
    guardWithMessage (isScalarType initTy) ("iterate: non-scalar accumulator type is not supported")
    return (initTy,TmIterate n' init' succ')
