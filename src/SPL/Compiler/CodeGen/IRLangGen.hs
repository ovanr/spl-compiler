{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
module SPL.Compiler.CodeGen.IRLangGen where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.List as L
import qualified Data.Set as S
import Data.Bifunctor
import Control.Lens hiding (Snoc)
import Control.Monad.State
import GHC.Stack
import Control.Applicative

import SPL.Compiler.CodeGen.IRLang
import SPL.Compiler.CodeGen.IRLangGenLib
import SPL.Compiler.CodeGen.IRLangBuiltins
import SPL.Compiler.CodeGen.IRLangTConGen
import SPL.Compiler.Common.TypeFunc
import SPL.Compiler.Common.Misc
import qualified SPL.Compiler.SemanticAnalysis.Core as Core
import qualified SPL.Compiler.SemanticAnalysis.TypeCheck.TCon as Core
import qualified SPL.Compiler.SemanticAnalysis.TypeCheck as Core
import Data.Tuple.Extra ((&&&))

exprToIRInstr :: Core.CoreExpr -> IRMonad (Some1 Value)

exprToIRInstr (Core.IntExpr _ i) =
    pure (Some1 $ IRLit (IRInt $ fromInteger i))

exprToIRInstr (Core.CharExpr _ c) =
    pure (Some1 $ IRLit (IRChar c))

exprToIRInstr (Core.BoolExpr _ b) =
    pure (Some1 $ IRLit (IRBool b))

exprToIRInstr (Core.VarIdentifierExpr (Core.CoreIdentifier _ id)) = do
    Some1 var <- findVarByName id
    pure . Some1 . IRVar $ var

exprToIRInstr (Core.FunIdentifierExpr (Core.CoreIdentifier _ id)) = do
    Some1 (IRFunDecl' fun) <- findFunByName id
    pure . Some1 . IRLit . IRFun $ fun

exprToIRInstr (Core.OpExpr _ op e) = do
    someVal <- exprToIRInstr e

    case (op, someVal) of
        (Core.UnNeg, Some1 src@(IRVar (Var _ IRBoolType _))) -> do
            dstV <- mkTmpVar IRBoolType
            body <>= [ Not dstV src ]
            return (Some1 $ IRVar dstV)

        (Core.UnMinus, Some1 src@(IRVar (Var _ IRIntType _))) -> do
            dstV <- mkTmpVar IRIntType
            body <>= [ Neg dstV src ] 
            return (Some1 $ IRVar dstV)

        (Core.UnMinus, Some1 (IRLit dst@(IRInt i))) ->
            return (Some1 . IRLit $ IRInt (-1))

        (Core.UnNeg, Some1 (IRLit dst@(IRBool b))) ->
            return (Some1 . IRLit $ IRBool (not b))
        _ -> pureIRError

exprToIRInstr (Core.EmptyListExpr _ t) = do
    case coreTypeToIRType t of
        Some1 t@(IRListType elemT) -> do
            tmp <- mkTmpVar t
            body <>= [MkNilList tmp]
            pure (Some1 $ IRVar tmp)
        _ -> coreError

exprToIRInstr (Core.TupExpr _ e1 e2) = do
    Some1 src1 <- exprToIRInstr e1
    Some1 src2 <- exprToIRInstr e2
    tmp <- mkTmpVar (IRTupleType (getType src1) (getType src2))
    body <>= [MkTup tmp src1 src2]
    pure (Some1 (IRVar tmp))

exprToIRInstr e@(Core.Op2Expr loc e1 op e2) = do
    case op of
        Core.Plus -> handleSimpleOp IRIntType e1 Add e2
        Core.Minus -> handleSimpleOp IRIntType e1 Sub e2
        Core.Mul -> handleSimpleOp IRIntType e1 Mul e2
        Core.Div -> handleSimpleOp IRIntType e1 Div e2
        Core.Mod -> handleSimpleOp IRIntType e1 Mod e2
        Core.Pow -> mkPowCall
        Core.Equal -> handleEqOp e1 e2
        Core.Less  -> handleOrdOp e1 e2
        Core.Greater  -> exprToIRInstr $ greaterEqToNotLess e
        Core.LessEq  -> exprToIRInstr $ lessEqToEqOrLess e
        Core.GreaterEq  -> exprToIRInstr $ greaterEqToNotLess e
        Core.Nequal  -> exprToIRInstr $ nEqToNotEq e
        Core.Cons -> handleConsOp e1 e2
        Core.LogAnd -> handleSimpleOp IRBoolType e1 And e2
        Core.LogOr -> handleSimpleOp IRBoolType e1 Or e2
    where
        greaterToNotLessEq (Core.Op2Expr loc e1 Core.Greater e2) = 
            Core.OpExpr loc Core.UnNeg (Core.Op2Expr loc e1 Core.LessEq e2)
        greaterToNotLessEq _ = impossible
            
        lessEqToEqOrLess (Core.Op2Expr loc e1 Core.LessEq e2) =
            Core.Op2Expr loc (Core.Op2Expr loc e1 Core.Equal e2) 
                              Core.LogOr 
                             (Core.Op2Expr loc e1 Core.Less e2)
        lessEqToEqOrLess _ = impossible

        greaterEqToNotLess (Core.Op2Expr loc e1 Core.GreaterEq e2) = 
            Core.OpExpr loc Core.UnNeg (Core.Op2Expr loc e1 Core.Less e2)
        greaterEqToNotLess _ = impossible

        nEqToNotEq (Core.Op2Expr loc e1 Core.Nequal e2) = 
            Core.OpExpr loc Core.UnNeg (Core.Op2Expr loc e1 Core.Equal e2)
        nEqToNotEq _ = impossible

        mkPowCall :: IRMonad (Some1 Value)
        mkPowCall = do 
            arg1 <- exprToIRInstr e1
            arg2 <- exprToIRInstr e2
            Some1 var <- callFunByName "_pow" [arg1, arg2]
            pure . Some1 . IRVar $ var

        handleSimpleOp :: IRType a ->
                          Core.CoreExpr ->
                          (Var a -> Value a -> Value a -> IRInstr) ->
                          Core.CoreExpr ->
                          IRMonad (Some1 Value)
        handleSimpleOp t e1 opInstr e2 = do
            (Some1 src1) <- exprToIRInstr e1
            (Some1 src2) <- exprToIRInstr e2
            dst <- mkTmpVar (getType t)
            whenTEq (IRVar dst) src1 $ \_ src1' -> do
                whenTEq (IRVar dst) src2 $ \(IRVar dst') src2' -> do
                    body <>= [opInstr dst' src1' src2']
                    return (Some1 $ IRVar dst')

        handleEqOp :: Core.CoreExpr -> Core.CoreExpr -> IRMonad (Some1 Value)
        handleEqOp e1 e2 = do
            src1@(Some1 src1') <- exprToIRInstr e1
            src2 <- exprToIRInstr e2
            solver <- resolveTCon (TEq $ getType src1')
            dst <- callFunWith solver [src1, src2]
            pure . Some1 . IRVar $ dst

        handleOrdOp :: Core.CoreExpr -> Core.CoreExpr -> IRMonad (Some1 Value)
        handleOrdOp e1 e2 = do
            src1@(Some1 src1') <- exprToIRInstr e1
            src2 <- exprToIRInstr e2
            solver <- resolveTCon (TOrd $ getType src1')
            dst <- callFunWith solver [src1, src2]
            pure . Some1 . IRVar $ dst

        handleConsOp :: Core.CoreExpr -> Core.CoreExpr -> IRMonad (Some1 Value)
        handleConsOp e1 e2 = do
            (Some1 elem) <- exprToIRInstr e1
            (Some1 (IRVar list@(Var _ listT@(IRListType elemT) _))) <- exprToIRInstr e2
            elem' <- cast elem elemT
            dst <- mkTmpVar (getType listT)
            body <>= [ConsList dst list elem'] 
            return (Some1 $ IRVar dst)

exprToIRInstr (Core.FunCallExpr f) = fmapSome IRVar <$> funCallToIRInstr f

mkFieldSelectorCall :: Var a -> [ Some1 IRFunDecl' ] -> IRMonad (Some1 Var)
mkFieldSelectorCall src [] = pure (Some1 src)
mkFieldSelectorCall src (Some1 (IRFunDecl' f): fs) = do
    let args = f ^. funArgs
        retType = f ^. funRetType
    case args of
        (arg :+: HNil) -> do
            concreteArg' <- castVar src (getType arg)
            dst <- mkTmpVar retType
            body <>= [ Call dst (IRLit $ IRFun f) (IRVar concreteArg' :+: HNil) ]
            mkFieldSelectorCall dst fs
        _ -> coreError

funCallToIRInstr :: Core.CoreFunCall -> IRMonad (Some1 Var)

funCallToIRInstr (Core.CoreFunCall _ e t@(Core.CoreFunType _ tcons _ retType) args) = do
    let tcons' = map coreTConToIRTCon tcons
    conVars <- mapM (\(Some1 t) -> Some1 <$> resolveTCon t) tcons'

    Some1 fun <- exprToIRInstr e
    argVars <- mapM exprToIRInstr args
    
    case fun of
        IRVar (Var _ IRFunType{} _) -> do 
            dst <- callFunWith fun (conVars ++ argVars)
            case coreTypeToIRType retType of
                Some1 concreteRetType -> Some1 <$> castVar dst concreteRetType

        IRLit IRFun{} -> do
            dst <- callFunWith fun (conVars ++ argVars)
            case coreTypeToIRType retType of
                Some1 concreteRetType ->  do
                    Some1 <$> castVar dst concreteRetType

        _ -> coreError

funCallToIRInstr _ = coreError


stmtToIRInstr :: Core.CoreStmt -> IRMonad ()

stmtToIRInstr (Core.IfElseStmt _ e stmts1 stmts2) = do
    ifElse <- mkLabel "IfElse"
    ifEnd <- mkLabel "IfEnd"
    Some1 cond <- exprToIRInstr e
    case getType cond of
        IRBoolType -> do
            body <>= [ BrFalse cond ifElse ]
            mapM_ stmtToIRInstr stmts1
            body <>= [ BrAlways ifEnd ]
            body <>= [ SetLabel ifElse ]
            mapM_ stmtToIRInstr stmts2
            body <>= [ SetLabel ifEnd ]
        _ -> coreError

stmtToIRInstr (Core.WhileStmt _ e stmts) = do
    whileStart <- mkLabel "WhileStart"
    whileEnd <- mkLabel "WhileEnd"
    body <>= [ SetLabel whileStart ]
    Some1 cond <- exprToIRInstr e
    case getType cond of
        IRBoolType -> do
            body <>= [ BrFalse cond whileEnd ]
            mapM_ stmtToIRInstr stmts
            body <>= [ BrAlways whileStart ]
            body <>= [ SetLabel whileEnd ]
        _ -> coreError


stmtToIRInstr (Core.AssignStmt _ (Core.CoreIdentifier _ id) t fields e) = do
    Some1 src <- findVarByName id
    funDecls <- mapM findFunByName $ getFunNames fields
    Some1 dst' <- case funDecls of
        [] -> Some1 <$> getRef src
        _ -> mkFieldSelectorCall src funDecls

    Some1 dst@(Var _ IRPtrType{} _) <- case coreTypeToIRType t of
        Some1 concreteRetType -> Some1 <$> castVar dst' (IRPtrType concreteRetType)

    Some1 src <- exprToIRInstr e
    whenPtrTEq dst src $
        \dst' src' ->
            body <>= [StoreA dst' src']

    where
        getFunNames :: [Core.Field] -> [Identifier]
        getFunNames [] = []
        getFunNames [x] = ["0" <> T.pack (show x) <> "_assign"]
        getFunNames (x:xs) = T.pack (show x) : getFunNames xs

stmtToIRInstr (Core.FunCallStmt fc) = void $ funCallToIRInstr fc

stmtToIRInstr (Core.ReturnStmt _ ma) = do
    case ma of
        Nothing -> do
            body <>= [ Ret $ IRLit IRVoid ]
        Just e -> do
            (Some1 dst) <- exprToIRInstr e
            body <>= [Ret dst]

varDeclToIRGlobal :: Core.CoreVarDecl -> IRMonad (Some1 IRGlobal)
varDeclToIRGlobal (Core.CoreVarDecl _ t (Core.CoreIdentifier _ id) e) =
    case coreTypeToIRType t of
        Some1 ct -> do
            let dst = Var id ct Global
            Some1 src <- exprToIRInstr e
            whenTEq dst src $ \dst' src' -> do
                body <>= [StoreV dst' src']
                pure . Some1 $ IRGlobal dst'

localVarDeclToIRInstr :: Core.CoreVarDecl -> IRMonad (Some1 Var)
localVarDeclToIRInstr (Core.CoreVarDecl _ t (Core.CoreIdentifier _ id) e) =
    case coreTypeToIRType t of
        Some1 ct -> do
            let dst = Var id ct Local
            Some1 src <- exprToIRInstr e
            src' <- cast src ct
            body <>= [DeclareV dst, StoreV dst src']
            vars %= (\(Some1 varCtx) -> Some1 $ dst :+: varCtx)
            pure $ Some1 dst

mkTConArgs :: [Core.TCon] -> IRMonad (Some1 (HList Var))
mkTConArgs [] = pure (Some1 HNil)
mkTConArgs (tcon:xs) = do
    argName <-
        case tcon of
            Core.TPrint _ -> mkName "print_con"
            Core.TEq _ -> mkName "eq_con"
            Core.TOrd _ -> mkName "ord_con"

    Some1 tconArgs <- mkTConArgs xs
    case coreTConToIRType tcon of
        Some1 t -> pure . Some1 $ Var argName t Local :+: tconArgs

mkFunArgs :: [Core.CoreIdentifier] -> [Core.CoreType] -> Some1 (HList Var)
mkFunArgs args argTypes =
    let argNames = map (\(Core.CoreIdentifier _ idName) -> idName) args
        argTypes' = map coreTypeToIRType argTypes
    in foldr (\(name, Some1 t) (Some1 acc) -> Some1 (Var name t Local :+: acc)) 
             (Some1 HNil) 
             (zip argNames argTypes')

funDeclToIRFunDecl :: Core.CoreFunDecl -> IRMonad (Some1 IRFunDecl')
funDeclToIRFunDecl (Core.CoreFunDecl _ (Core.CoreIdentifier _ id) args (Core.CoreFunType _ tcons as r) _) = do
    Some1 conVars <- mkTConArgs tcons
    case (mkFunArgs args as, coreTypeToIRType r) of
        (Some1 argVars, Some1 retType) -> do
            return . Some1 . IRFunDecl' $ IRFunDecl id (conVars +++ argVars) retType
funDeclToIRFunDecl _ = coreError

funDeclToIRInstr :: IRFunDecl' xs -> Core.CoreFunBody -> IRMonad (Some1 IRFunDef)
funDeclToIRInstr decl@(IRFunDecl' (IRFunDecl _ args _)) (Core.CoreFunBody _ varDecls stmts) = do
    vars %= \(Some1 varCtx) -> Some1 (args +++ varCtx)
    funBody <- declareBodyAs $ do
        mapM_ localVarDeclToIRInstr varDecls
        mapM_ stmtToIRInstr stmts
    return . Some1 $ IRFunDef decl funBody

mkTConFuncs :: IRMonad [Some1 IRFunDef]
mkTConFuncs = do
    Some1 tcons <- use neededTConGen
    concat <$> mapM solveTConConstraint (hListToList tcons)

mkStartFun :: [IRInstr] -> IRMonad (IRFunDef '[Unit])
mkStartFun globalVarInitInstr = do
    let startFunDecl = IRFunDecl' (IRFunDecl "_start" HNil IRVoidType)
    mainFun <- searchFunByName (== "main")
    case mainFun of
        Nothing -> pure $ IRFunDef startFunDecl (globalVarInitInstr ++ [Halt])
        Just (Some1 (IRFunDecl' main@(IRFunDecl _ args _))) -> do
            funBody <- declareBodyAs $ do
                body <>= globalVarInitInstr
                callFunByName "main" []
                body <>= [Halt]
            pure (IRFunDef startFunDecl funBody)

coreToIRLang :: Core.Core -> IRMonad (Some2 IRLang)
coreToIRLang (Core.Core varDecls userFunDecls) = do
    userFunCtx <- hListFromList <$> mapM funDeclToIRFunDecl userFunDecls

    Some1 builtinDefs <- mkBuiltins

    funcs .= liftA2Some (\x y -> Some1 (x +++ y))
                userFunCtx
                (hListMap (Some1 . _funDecl) builtinDefs)

    let voidVar = Var "_void_var" IRVoidType Global
    Some1 globalDecls <- hListFromList . (Some1 (IRGlobal voidVar) :) <$> mapM varDeclToIRGlobal varDecls
    globVarInitBody <- use body
    body .= []

    Some1 coreGlobals <- pure $ hListMap (\(IRGlobal v) -> Some1 v) globalDecls

    Some1 userFunDefs <-
        hListFromList <$>
            forM userFunDecls (\(Core.CoreFunDecl _ (Core.CoreIdentifier _ id) _ _ funBody) -> do
                vars .= Some1 coreGlobals
                Some1 funDecl <- findFunByName id
                funDeclToIRInstr funDecl funBody)

    Some1 tconAllFunDefs <- hListFromList <$> mkTConFuncs

    startFuncDef <- mkStartFun globVarInitBody

    return . Some2 $ IRLang globalDecls
                            (builtinDefs +++ tconAllFunDefs +++ userFunDefs +++ startFuncDef :+: HNil)

performIRLangGen :: Core.Core -> Either Text (Some2 IRLang)
performIRLangGen core = do
    let clState = IRState (Some1 HNil) (Some1 HNil) [] (Some1 HNil) 1 1
    evalStateT (coreToIRLang core) clState
