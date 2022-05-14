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
import qualified SPL.Compiler.SemanticAnalysis.TCT as TCT
import qualified SPL.Compiler.SemanticAnalysis.TypeCheck.TCon as TCT
import qualified SPL.Compiler.SemanticAnalysis.TypeCheck as TCT

exprToIRInstr ::TCT.TCTExpr -> IRMonad (Some1 Var)

exprToIRInstr (TCT.IntExpr _ i) = do
    tmp <- mkTmpVar IRIntType
    body <>= [StoreI tmp (fromInteger i)]
    pure (Some1 tmp)

exprToIRInstr (TCT.CharExpr _ c) = do
    tmp <- mkTmpVar IRCharType
    body <>= [StoreC tmp c ]
    pure (Some1 tmp)

exprToIRInstr (TCT.BoolExpr _ b) = do
    tmp <- mkTmpVar IRBoolType
    body <>= [StoreB tmp b ]
    pure (Some1 tmp)

exprToIRInstr (TCT.OpExpr _ op e) = do
    someVar1 <- exprToIRInstr e
    body <>= case (op, someVar1) of
        (TCT.UnNeg, Some1 dst@(Var _ IRBoolType)) -> [ Not dst dst ]
        (TCT.UnMinus, Some1 dst@(Var _ IRIntType)) -> [ Neg dst dst ]
        _ -> pureIRError
    pure someVar1

exprToIRInstr (TCT.EmptyListExpr _ t) = do
    case tctTypeToIRType t [] of
        Some1 t@(IRListType elemT) -> do
            tmp <- mkTmpVar t
            body <>= [MkNilList tmp]
            pure (Some1 tmp)
        _ -> coreError

exprToIRInstr (TCT.TupExpr _ e1 e2) = do
    (Some1 src1@(Var _ ct1)) <- exprToIRInstr e1
    (Some1 src2@(Var _ ct2)) <- exprToIRInstr e2
    tmp <- mkTmpVar (IRTupleType ct1 ct2)
    body <>= [MkTup tmp src1 src2]
    pure (Some1 tmp)

exprToIRInstr e@(TCT.Op2Expr loc e1 op e2) = do
    case op of
        TCT.Plus -> handleSimpleOp IRIntType e1 Add e2
        TCT.Minus -> handleSimpleOp IRIntType e1 Sub e2
        TCT.Mul -> handleSimpleOp IRIntType e1 Mul e2
        TCT.Div -> handleSimpleOp IRIntType e1 Div e2
        TCT.Mod -> handleSimpleOp IRIntType e1 Mod e2
        TCT.Pow -> exprToIRInstr $ mkPowCall loc e1 e2
        TCT.Equal -> handleOverloadedOp (T.isPrefixOf "0eq_con") e1 e2
        TCT.Less  -> handleOverloadedOp (T.isPrefixOf "0ord_con") e1 e2
        TCT.Greater  -> exprToIRInstr $ greaterEqIsNotLess loc e1 e2
        TCT.LessEq  -> exprToIRInstr $ lessEqIsEqOrLess loc e1 e2
        TCT.GreaterEq  -> exprToIRInstr $ greaterEqIsNotLess loc e1 e2
        TCT.Nequal  -> exprToIRInstr $ nEqIsNotEq loc e1 e2
        TCT.Cons -> handleConsOp e1 e2
        TCT.LogAnd -> handleSimpleOp IRBoolType e1 And e2
        TCT.LogOr -> handleSimpleOp IRBoolType e1 Or e2
    where
        greaterIsNotLessEq loc e1 e2 = TCT.OpExpr loc TCT.UnNeg (TCT.Op2Expr loc e1 TCT.LessEq e2)
        lessEqIsEqOrLess loc e1 e2 =
            TCT.Op2Expr loc (TCT.Op2Expr loc e1 TCT.Equal e2) TCT.LogOr (TCT.Op2Expr loc e1 TCT.Less e2)
        greaterEqIsNotLess loc e1 e2 = TCT.OpExpr loc TCT.UnNeg (TCT.Op2Expr loc e1 TCT.Less e2)
        nEqIsNotEq loc e1 e2 = TCT.OpExpr loc TCT.UnNeg $ TCT.Op2Expr loc e1 TCT.Equal e2
        mkPowCall loc e1 e2 = 
            TCT.FunCallExpr $ 
                TCT.TCTFunCall loc 
                               (TCT.TCTIdentifier loc "0pow") 
                               (TCT.TCTFunType loc (TCT.TCTIntType loc) 
                                                   (TCT.TCTFunType loc (TCT.TCTIntType loc)
                                                                       (TCT.TCTIntType loc)))
                               []
                               [e1, e2]
        handleSimpleOp :: IRType a ->
                          TCT.TCTExpr ->
                          (Var a -> Var a -> Var a -> IRInstr) ->
                          TCT.TCTExpr ->
                          IRMonad (Some1 Var)
        handleSimpleOp t e1 opInstr e2 = do
            (Some1 src1) <- exprToIRInstr e1
            (Some1 src2) <- exprToIRInstr e2
            tmp <- mkTmpVar t
            whenVarTEq tmp src1 $ \tmp' src1' ->
                whenVarTEq src1' src2 $ \src1'' src2' -> do
                    body <>= [opInstr tmp' src1'' src2' ]
                    return (Some1 tmp')

        handleOverloadedOp :: (Identifier -> Bool) ->
                              TCT.TCTExpr ->
                              TCT.TCTExpr ->
                              IRMonad (Some1 Var)
        handleOverloadedOp varConPredicate e1 e2 = do
            (Some1 src1@(Var _ arg1T)) <- exprToIRInstr e1
            (Some1 src2@(Var _ arg2T)) <- exprToIRInstr e2
            let conType = IRFunType (arg1T :+: arg2T :+: HNil) IRBoolType
            solver <- findVar varConPredicate conType
            dst <- mkTmpVar IRBoolType
            body <>= [CallV dst solver (src1 :+: src2 :+: HNil)]
            return $ Some1 dst

        handleConsOp :: TCT.TCTExpr ->
                        TCT.TCTExpr ->
                        IRMonad (Some1 Var)
        handleConsOp e1 e2 = do
            (Some1 elem) <- exprToIRInstr e1
            (Some1 list@(Var _ lct@(IRListType _))) <- exprToIRInstr e2
            whenVarTListEq list elem $ \list' elem' -> do
                tmp <- mkTmpVar lct
                body <>= [ConsList tmp list' elem']
                return (Some1 tmp)

exprToIRInstr (TCT.FunCallExpr f) = funCallToIRInstr f

exprToIRInstr (TCT.FieldSelectExpr (TCT.TCTFieldSelector _ (TCT.TCTIdentifier _ id) tau fds)) = do
    Some1 src <- findVarByName id
    funDecl <- mapM (findFunByName . tctFieldToId) fds
    Some1 dst@(Var _ dstT) <- mkFieldSelectorCall src funDecl
    if hasUnknownType dstT then
        case tctTypeToIRType tau [] of
            Some1 concreteRetType -> Some1 <$> unsafeCast dst concreteRetType
    else
        pure $ Some1 dst

    where
        tctFieldToId = T.pack . show

mkFieldSelectorCall :: Var a -> [ Some1 IRFunDecl' ] -> IRMonad (Some1 Var)
mkFieldSelectorCall src [] = pure (Some1 src)
mkFieldSelectorCall src (Some1 (IRFunDecl' f): fs) = do
    let args = f ^. funArgs
        retType = f ^. funRetType
    case args of
        (arg :+: HNil) -> do
            concreteArg' <- castFunArg arg src
            dst <- mkTmpVar retType
            body <>= [ Call dst f (concreteArg' :+: HNil) ]
            mkFieldSelectorCall dst fs
        _ -> coreError

funCallToIRInstr :: TCT.TCTFunCall -> IRMonad (Some1 Var)
funCallToIRInstr (TCT.TCTFunCall _ (TCT.TCTIdentifier _ "print") _ _ args) = do
    [Some1 arg@(Var _ argT)] <- mapM exprToIRInstr args
    let printType = IRFunType (argT :+: HNil) IRVoidType
    conVar <- findVar (T.isPrefixOf "0print_con") printType
    dst <- mkTmpVar IRVoidType
    body <>= [CallV dst conVar (arg :+: HNil)]
    return (Some1 dst)

funCallToIRInstr (TCT.TCTFunCall _ (TCT.TCTIdentifier _ id) tau tcons args) = do
    conVars <- mapM findConVar tcons
    argVars <- mapM exprToIRInstr args

    Some1 dst <- callFunWith id (conVars ++ argVars)
    case tctTypeToIRType (TCT.getReturnType tau) [] of
        Some1 concreteRetType -> Some1 <$> unsafeCast dst concreteRetType

fieldSelectorStmtToIRInstr :: TCT.TCTFieldSelector ->
                                IRMonad (Some1 Var)
fieldSelectorStmtToIRInstr (TCT.TCTFieldSelector _ (TCT.TCTIdentifier _ id) tau fds) = do
    Some1 src <- findVarByName id
    funDecls <- mapM findFunByName $ getFunNames fds
    Some1 dst <- case funDecls of
        [] -> Some1 <$> getRef src
        _ -> mkFieldSelectorCall src funDecls
    case tctTypeToIRType tau [] of
        Some1 concreteRetType -> Some1 <$> unsafeCast dst (IRPtrType concreteRetType)

    where
        getFunNames :: [TCT.TCTField] -> [Identifier]
        getFunNames [] = []
        getFunNames [x] = ["0" <> T.pack (show x) <> "_assign"]
        getFunNames (x:xs) = T.pack (show x) : getFunNames xs


stmtToIRInstr :: TCT.TCTStmt -> IRMonad ()

stmtToIRInstr (TCT.IfElseStmt _ e stmts1 stmts2) = do
    ifElse <- mkLabel "IfElse"
    ifEnd <- mkLabel "IfEnd"
    Some1 cond@(Var _ IRBoolType) <- exprToIRInstr e
    body <>= [ BrFalse cond ifElse ]
    mapM_ stmtToIRInstr stmts1
    body <>= [ BrAlways ifEnd ]
    body <>= [ SetLabel ifElse ]
    mapM_ stmtToIRInstr stmts2
    body <>= [ SetLabel ifEnd ]

stmtToIRInstr (TCT.WhileStmt _ e stmts) = do
    whileStart <- mkLabel "WhileStart"
    whileEnd <- mkLabel "WhileEnd"
    body <>= [ SetLabel whileStart ]
    Some1 cond@(Var _ IRBoolType) <- exprToIRInstr e
    body <>= [ BrFalse cond whileEnd ]
    mapM_ stmtToIRInstr stmts
    body <>= [ BrAlways whileStart ]
    body <>= [ SetLabel whileEnd ]

stmtToIRInstr (TCT.AssignStmt _ fd e) = do
    Some1 (Var dstId (IRPtrType dstT)) <- fieldSelectorStmtToIRInstr fd
    Some1 (Var srcId srcT) <- exprToIRInstr e
    whenIRTypeEq dstT srcT $
        \dstT' srcT' ->
            body <>= [StoreA (Var dstId (IRPtrType dstT')) (Var srcId srcT')]

stmtToIRInstr (TCT.FunCallStmt _ fc) = void $ funCallToIRInstr fc

stmtToIRInstr (TCT.ReturnStmt _ ma) = do
    case ma of
        Nothing -> do
            voidVar <- mkTmpVar IRVoidType
            body <>= [ RetV voidVar ]
        Just e -> do
            (Some1 dst) <- exprToIRInstr e
            body <>= [RetV dst]

varDeclToIRGlobal :: TCT.TCTVarDecl -> IRMonad (Some1 IRGlobal)
varDeclToIRGlobal (TCT.TCTVarDecl _ t (TCT.TCTIdentifier _ id) e) =
    case tctTypeToIRType t [] of
        Some1 ct -> do
            let dst = Var id ct
            Some1 src <- exprToIRInstr e
            whenVarTEq dst src $ \dst' src' -> do
                body <>= [StoreV dst' src']
                pure . Some1 $ IRGlobal dst'

varDeclToIRInstr :: TCT.TCTVarDecl -> IRMonad (Some1 Var)
varDeclToIRInstr (TCT.TCTVarDecl _ t (TCT.TCTIdentifier _ id) e) =
    case tctTypeToIRType t [] of
        Some1 ct -> do
            let dst = Var id ct
            Some1 src <- exprToIRInstr e
            whenVarTEq dst src $ \dst' src' -> do
                body <>= [Declare dst', StoreV dst' src']
                vars %= (\(Some1 varCtx) -> Some1 $ dst' :+: varCtx)
                pure $ Some1 dst'

mkTConArgs :: [TCT.TCon] -> IRMonad (Some1 (HList Var))
mkTConArgs [] = pure (Some1 HNil)
mkTConArgs (tcon:xs) = do
    argName <-
        case tcon of
            TCT.TPrint _ -> mkName "print_con"
            TCT.TEq _ -> mkName "eq_con"
            TCT.TOrd _ -> mkName "ord_con"

    Some1 tconArgs <- mkTConArgs xs
    case tctTConToIRType tcon of
        Some1 t -> pure . Some1 $ Var argName t :+: tconArgs

mkFunArgs :: [TCT.TCTIdentifier] -> TCT.TCTType -> Some1 (HList Var)
mkFunArgs [] retType = Some1 HNil
mkFunArgs ((TCT.TCTIdentifier _ id):xs) (TCT.TCTFunType _ ta tb) = do
    case (tctTypeToIRType ta [], mkFunArgs xs tb) of
        (Some1 cta, Some1 vars) -> Some1 (Var id cta :+: vars)
mkFunArgs _ _ = pureIRError

funDeclToIRFunDecl :: TCT.TCTFunDecl -> IRMonad (Some1 IRFunDecl')
funDeclToIRFunDecl (TCT.TCTFunDecl _ (TCT.TCTIdentifier _ id) args tau tcons _) = do
    Some1 conVars <- mkTConArgs tcons

    case (mkFunArgs args tau, tctTypeToIRType (TCT.getReturnType tau) []) of
        (Some1 argVars, Some1 retType) -> do
            return . Some1 . IRFunDecl' $ IRFunDecl id (conVars +++ argVars) retType

funDeclToIRInstr :: IRFunDecl' xs -> TCT.TCTFunBody -> IRMonad (Some1 IRFunDef)
funDeclToIRInstr decl@(IRFunDecl' (IRFunDecl _ args _)) (TCT.TCTFunBody _ varDecls stmts) = do
    vars %= \(Some1 varCtx) -> Some1 (args +++ varCtx)
    funBody <- declareBodyAs $ do
        mapM_ varDeclToIRInstr varDecls
        mapM_ stmtToIRInstr stmts
    return . Some1 $ IRFunDef decl funBody

mkTConFuncs :: IRMonad [Some1 IRFunDef]
mkTConFuncs = do
    mainFun <- searchFunByName (== "main")
    case mainFun of 
        Nothing -> pure []
        Just (Some1 (IRFunDecl' mainFun')) -> solveFunDeclConstraints mainFun'

mkStartFun :: [IRInstr] -> HList IRFunDecl' xs -> IRMonad (IRFunDef '[Unit])
mkStartFun globalVarInitInstr tconFuncs = do
    let startFunDecl = IRFunDecl' (IRFunDecl "0start" HNil IRVoidType)
    mainFun <- searchFunByName (== "main")
    case mainFun of
        Nothing -> pure $ IRFunDef startFunDecl (globalVarInitInstr ++ [Halt])
        Just (Some1 (IRFunDecl' main@(IRFunDecl _ args _))) -> do
            funBody <- declareBodyAs $ do
                body <>= globalVarInitInstr
                funArgs <- forM (hListToList tconFuncs) (\(Some1 (IRFunDecl' f)) -> do 
                    tmp <- mkTmpVar (getFunType f) 
                    body <>= [StoreL tmp f]
                    return (Some1 tmp))
                callFunWith "main" funArgs
                body <>= [Halt]
            pure (IRFunDef startFunDecl funBody)

tctToIRLang :: TCT.TCT -> IRMonad (Some2 IRLang)
tctToIRLang (TCT.TCT varDecls userFunDecls) = do
    let userFunDecls' = concat userFunDecls

    userFunCtx <- hListFromList <$> mapM funDeclToIRFunDecl userFunDecls'

    Some1 builtinDefs <- mkBuiltins

    funcs .= liftA2Some (\x y -> Some1 (x +++ y))
                userFunCtx
                (hListMap (Some1 . _funDecl) builtinDefs)

    Some1 globalDecls <- hListFromList <$> mapM varDeclToIRGlobal varDecls
    globVarInitBody <- use body
    body .= []

    Some1 coreGlobals <- pure $ hListMap (\(IRGlobal v) -> Some1 v) globalDecls

    Some1 userFunDefs <-
        hListFromList <$> 
            forM userFunDecls' (\(TCT.TCTFunDecl _ (TCT.TCTIdentifier _ id) _ _ tcons funBody) -> do
                vars .= Some1 coreGlobals
                Some1 funDecl <- findFunByName id
                funDeclToIRInstr funDecl funBody)

    Some1 tconFunDefs <- hListFromList <$> mkTConFuncs

    startFuncDef <- mkStartFun globVarInitBody $ hListTCMap (\(IRFunDef decl _) -> decl) tconFunDefs

    return . Some2 $ IRLang globalDecls 
                              (builtinDefs +++ tconFunDefs +++ userFunDefs +++ startFuncDef :+: HNil)

performIRLangGen :: TCT.TCT -> Either Text (Some2 IRLang)
performIRLangGen tct = do
    let clState = IRState (Some1 HNil) (Some1 HNil) [] 1 1
    evalStateT (tctToIRLang tct) clState
