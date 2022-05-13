{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
module SPL.Compiler.CodeGen.CoreLangGen where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.List as L
import qualified Data.Set as S
import Data.Bifunctor
import Control.Lens hiding (Snoc)
import Control.Monad.State
import GHC.Stack
import Control.Applicative

import SPL.Compiler.CodeGen.CoreLang
import SPL.Compiler.CodeGen.CoreLangGenLib
import SPL.Compiler.CodeGen.CoreLangBuiltins
import SPL.Compiler.CodeGen.CoreLangTConGen
import SPL.Compiler.Common.TypeFunc
import qualified SPL.Compiler.SemanticAnalysis.TCT as TCT
import qualified SPL.Compiler.SemanticAnalysis.TypeCheck.TCon as TCT
import qualified SPL.Compiler.SemanticAnalysis.TypeCheck as TCT

exprToCoreInstr ::TCT.TCTExpr -> CoreMonad (Some1 Var)

exprToCoreInstr (TCT.IntExpr _ i) = do
    tmp <- mkTmpVar CoreIntType
    body <>= [StoreI tmp (fromInteger i)]
    pure (Some1 tmp)

exprToCoreInstr (TCT.CharExpr _ c) = do
    tmp <- mkTmpVar CoreCharType
    body <>= [StoreC tmp c ]
    pure (Some1 tmp)

exprToCoreInstr (TCT.BoolExpr _ b) = do
    tmp <- mkTmpVar CoreBoolType
    body <>= [StoreB tmp b ]
    pure (Some1 tmp)

exprToCoreInstr (TCT.OpExpr _ op e) = do
    someVar1 <- exprToCoreInstr e
    body <>= case (op, someVar1) of
        (TCT.UnNeg, Some1 dst@(Var _ CoreBoolType)) -> [ Not dst dst ]
        (TCT.UnMinus, Some1 dst@(Var _ CoreIntType)) -> [ Neg dst dst ]
        _ -> pureCoreError
    pure someVar1

exprToCoreInstr (TCT.EmptyListExpr _ t) = do
    case tctTypeToCoreType t [] of
        Some1 t@(CoreListType elemT) -> do
            tmp <- mkTmpVar t
            body <>= [MkNilList tmp]
            pure (Some1 tmp)
        _ -> coreError

exprToCoreInstr (TCT.TupExpr _ e1 e2) = do
    (Some1 src1@(Var _ ct1)) <- exprToCoreInstr e1
    (Some1 src2@(Var _ ct2)) <- exprToCoreInstr e2
    tmp <- mkTmpVar (CoreTupleType ct1 ct2)
    body <>= [MkTup tmp src1 src2]
    pure (Some1 tmp)

exprToCoreInstr e@(TCT.Op2Expr loc e1 op e2) = do
    case op of
        TCT.Plus -> handleSimpleOp CoreIntType e1 Add e2
        TCT.Minus -> handleSimpleOp CoreIntType e1 Sub e2
        TCT.Mul -> handleSimpleOp CoreIntType e1 Mul e2
        TCT.Div -> handleSimpleOp CoreIntType e1 Div e2
        TCT.Mod -> handleSimpleOp CoreIntType e1 Mod e2
        TCT.Pow -> exprToCoreInstr $ mkPowCall loc e1 e2
        TCT.Equal -> handleOverloadedOp (T.isPrefixOf "0eq_con") e1 e2
        TCT.Less  -> handleOverloadedOp (T.isPrefixOf "0ord_con") e1 e2
        TCT.Greater  -> exprToCoreInstr $ greaterEqIsNotLess loc e1 e2
        TCT.LessEq  -> exprToCoreInstr $ lessEqIsEqOrLess loc e1 e2
        TCT.GreaterEq  -> exprToCoreInstr $ greaterEqIsNotLess loc e1 e2
        TCT.Nequal  -> exprToCoreInstr $ nEqIsNotEq loc e1 e2
        TCT.Cons -> handleConsOp e1 e2
        TCT.LogAnd -> handleSimpleOp CoreBoolType e1 And e2
        TCT.LogOr -> handleSimpleOp CoreBoolType e1 Or e2
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
        handleSimpleOp :: CoreType a ->
                          TCT.TCTExpr ->
                          (Var a -> Var a -> Var a -> CoreInstr) ->
                          TCT.TCTExpr ->
                          CoreMonad (Some1 Var)
        handleSimpleOp t e1 opInstr e2 = do
            (Some1 src1) <- exprToCoreInstr e1
            (Some1 src2) <- exprToCoreInstr e2
            tmp <- mkTmpVar t
            whenVarTEq tmp src1 $ \tmp' src1' ->
                whenVarTEq src1' src2 $ \src1'' src2' -> do
                    body <>= [opInstr tmp' src1'' src2' ]
                    return (Some1 tmp')

        handleOverloadedOp :: (Identifier -> Bool) ->
                              TCT.TCTExpr ->
                              TCT.TCTExpr ->
                              CoreMonad (Some1 Var)
        handleOverloadedOp varConPredicate e1 e2 = do
            (Some1 src1@(Var _ arg1T)) <- exprToCoreInstr e1
            (Some1 src2@(Var _ arg2T)) <- exprToCoreInstr e2
            let conType = CoreFunType (arg1T :+: arg2T :+: HNil) CoreBoolType
            solver <- findVar varConPredicate conType
            dst <- mkTmpVar CoreBoolType
            body <>= [CallV dst solver (src1 :+: src2 :+: HNil)]
            return $ Some1 dst

        handleConsOp :: TCT.TCTExpr ->
                        TCT.TCTExpr ->
                        CoreMonad (Some1 Var)
        handleConsOp e1 e2 = do
            (Some1 elem) <- exprToCoreInstr e1
            (Some1 list@(Var _ lct@(CoreListType _))) <- exprToCoreInstr e2
            whenVarTListEq list elem $ \list' elem' -> do
                tmp <- mkTmpVar lct
                body <>= [ConsList tmp list' elem']
                return (Some1 tmp)

exprToCoreInstr (TCT.FunCallExpr f) = funCallToCoreInstr f

exprToCoreInstr (TCT.FieldSelectExpr (TCT.TCTFieldSelector _ (TCT.TCTIdentifier _ id) tau fds)) = do
    Some1 src <- findVarByName id
    funDecl <- mapM (findFunByName . tctFieldToId) fds
    Some1 dst@(Var _ dstT) <- mkFieldSelectorCall src funDecl
    if hasUnknownType dstT then
        case tctTypeToCoreType tau [] of
            Some1 concreteRetType -> Some1 <$> unsafeCast dst concreteRetType
    else
        pure $ Some1 dst

    where
        tctFieldToId = T.pack . show

mkFieldSelectorCall :: Var a -> [ Some1 CoreFunDecl' ] -> CoreMonad (Some1 Var)
mkFieldSelectorCall src [] = pure (Some1 src)
mkFieldSelectorCall src (Some1 (CoreFunDecl' f): fs) = do
    let args = f ^. funArgs
        retType = f ^. funRetType
    case args of
        (arg :+: HNil) -> do
            concreteArg' <- castFunArg arg src
            dst <- mkTmpVar retType
            body <>= [ Call dst f (concreteArg' :+: HNil) ]
            mkFieldSelectorCall dst fs
        _ -> coreError

funCallToCoreInstr :: TCT.TCTFunCall -> CoreMonad (Some1 Var)
funCallToCoreInstr (TCT.TCTFunCall _ (TCT.TCTIdentifier _ "print") _ _ args) = do
    [Some1 arg@(Var _ argT)] <- mapM exprToCoreInstr args
    let printType = CoreFunType (argT :+: HNil) CoreVoidType
    conVar <- findVar (T.isPrefixOf "0print_con") printType
    dst <- mkTmpVar CoreVoidType
    body <>= [CallV dst conVar (arg :+: HNil)]
    return (Some1 dst)

funCallToCoreInstr (TCT.TCTFunCall _ (TCT.TCTIdentifier _ id) tau tcons args) = do
    conVars <- mapM findConVar tcons
    argVars <- mapM exprToCoreInstr args

    Some1 dst <- callFunWith id (conVars ++ argVars)
    case tctTypeToCoreType (TCT.getReturnType tau) [] of
        Some1 concreteRetType -> Some1 <$> unsafeCast dst concreteRetType

fieldSelectorStmtToCoreInstr :: TCT.TCTFieldSelector ->
                                CoreMonad (Some1 Var)
fieldSelectorStmtToCoreInstr (TCT.TCTFieldSelector _ (TCT.TCTIdentifier _ id) tau fds) = do
    Some1 src <- findVarByName id
    funDecls <- mapM findFunByName $ getFunNames fds
    Some1 dst <- case funDecls of
        [] -> Some1 <$> getRef src
        _ -> mkFieldSelectorCall src funDecls
    case tctTypeToCoreType tau [] of
        Some1 concreteRetType -> Some1 <$> unsafeCast dst (CorePtrType concreteRetType)

    where
        getFunNames :: [TCT.TCTField] -> [Identifier]
        getFunNames [] = []
        getFunNames [x] = ["0" <> T.pack (show x) <> "_assign"]
        getFunNames (x:xs) = T.pack (show x) : getFunNames xs


stmtToCoreInstr :: TCT.TCTStmt -> CoreMonad ()

stmtToCoreInstr (TCT.IfElseStmt _ e stmts1 stmts2) = do
    ifElse <- mkLabel "IfElse"
    ifEnd <- mkLabel "IfEnd"
    Some1 cond@(Var _ CoreBoolType) <- exprToCoreInstr e
    body <>= [ BrFalse cond ifElse ]
    mapM_ stmtToCoreInstr stmts1
    body <>= [ BrAlways ifEnd ]
    body <>= [ SetLabel ifElse ]
    mapM_ stmtToCoreInstr stmts2
    body <>= [ SetLabel ifEnd ]

stmtToCoreInstr (TCT.WhileStmt _ e stmts) = do
    whileStart <- mkLabel "WhileStart"
    whileEnd <- mkLabel "WhileEnd"
    body <>= [ SetLabel whileStart ]
    Some1 cond@(Var _ CoreBoolType) <- exprToCoreInstr e
    body <>= [ BrFalse cond whileEnd ]
    mapM_ stmtToCoreInstr stmts
    body <>= [ BrAlways whileStart ]
    body <>= [ SetLabel whileEnd ]

stmtToCoreInstr (TCT.AssignStmt _ fd e) = do
    Some1 (Var dstId (CorePtrType dstT)) <- fieldSelectorStmtToCoreInstr fd
    Some1 (Var srcId srcT) <- exprToCoreInstr e
    whenCoreTypeEq dstT srcT $
        \dstT' srcT' ->
            body <>= [StoreA (Var dstId (CorePtrType dstT')) (Var srcId srcT')]

stmtToCoreInstr (TCT.FunCallStmt _ fc) = void $ funCallToCoreInstr fc

stmtToCoreInstr (TCT.ReturnStmt _ ma) = do
    case ma of
        Nothing -> do
            voidVar <- mkTmpVar CoreVoidType
            body <>= [ RetV voidVar ]
        Just e -> do
            (Some1 dst) <- exprToCoreInstr e
            body <>= [RetV dst]

varDeclToCoreGlobal :: TCT.TCTVarDecl -> CoreMonad (Some1 CoreGlobal)
varDeclToCoreGlobal (TCT.TCTVarDecl _ t (TCT.TCTIdentifier _ id) e) =
    case tctTypeToCoreType t [] of
        Some1 ct -> do
            let dst = Var id ct
            Some1 src <- exprToCoreInstr e
            whenVarTEq dst src $ \dst' src' -> do
                body <>= [Declare dst', StoreV dst' src']
                coreInstr <- use body
                pure . Some1 $ CoreGlobal dst' coreInstr

varDeclToCoreInstr :: TCT.TCTVarDecl -> CoreMonad (Some1 Var)
varDeclToCoreInstr (TCT.TCTVarDecl _ t (TCT.TCTIdentifier _ id) e) =
    case tctTypeToCoreType t [] of
        Some1 ct -> do
            let dst = Var id ct
            Some1 src <- exprToCoreInstr e
            whenVarTEq dst src $ \dst' src' -> do
                body <>= [Declare dst', StoreV dst' src']
                vars %= (\(Some1 varCtx) -> Some1 $ dst' :+: varCtx)
                pure $ Some1 dst'

mkTConArgs :: [TCT.TCon] -> CoreMonad (Some1 (HList Var))
mkTConArgs [] = pure (Some1 HNil)
mkTConArgs (tcon:xs) = do
    argName <-
        case tcon of
            TCT.TPrint _ -> mkName "print_con"
            TCT.TEq _ -> mkName "eq_con"
            TCT.TOrd _ -> mkName "ord_con"

    Some1 tconArgs <- mkTConArgs xs
    case tctTConToCoreType tcon of
        Some1 t -> pure . Some1 $ Var argName t :+: tconArgs

mkFunArgs :: [TCT.TCTIdentifier] -> TCT.TCTType -> Some1 (HList Var)
mkFunArgs [] retType = Some1 HNil
mkFunArgs ((TCT.TCTIdentifier _ id):xs) (TCT.TCTFunType _ ta tb) = do
    case (tctTypeToCoreType ta [], mkFunArgs xs tb) of
        (Some1 cta, Some1 vars) -> Some1 (Var id cta :+: vars)
mkFunArgs _ _ = pureCoreError

funDeclToCoreFunDecl :: TCT.TCTFunDecl -> CoreMonad (Some1 CoreFunDecl')
funDeclToCoreFunDecl (TCT.TCTFunDecl _ (TCT.TCTIdentifier _ id) args tau tcons _) = do
    Some1 conVars <- mkTConArgs tcons

    case (mkFunArgs args tau, tctTypeToCoreType (TCT.getReturnType tau) []) of
        (Some1 argVars, Some1 retType) -> do
            return . Some1 . CoreFunDecl' $ CoreFunDecl id (conVars +++ argVars) retType

funDeclToCoreInstr :: CoreFunDecl' xs -> TCT.TCTFunBody -> CoreMonad (Some1 CoreFunDef)
funDeclToCoreInstr decl@(CoreFunDecl' (CoreFunDecl _ args _)) (TCT.TCTFunBody _ varDecls stmts) = do
    vars %= \(Some1 varCtx) -> Some1 (args +++ varCtx)
    funBody <- declareBodyAs $ do
        mapM_ varDeclToCoreInstr varDecls
        mapM_ stmtToCoreInstr stmts
    return . Some1 $ CoreFunDef decl funBody

mkTConFuncs :: CoreMonad [Some1 CoreFunDef]
mkTConFuncs = do
    mainFun <- searchFunByName (== "main")
    case mainFun of 
        Nothing -> pure []
        Just (Some1 (CoreFunDecl' mainFun')) -> solveFunDeclConstraints mainFun'

mkStartFun :: HList CoreFunDecl' xs -> CoreMonad (CoreFunDef '[Unit])
mkStartFun tconFuncs = do
    let startFunDecl = CoreFunDecl' (CoreFunDecl "0start" HNil CoreVoidType)
    mainFun <- searchFunByName (== "main")
    case mainFun of
        Nothing -> pure $ CoreFunDef startFunDecl [Halt]
        Just (Some1 (CoreFunDecl' main@(CoreFunDecl _ args _))) -> do
            funBody <- declareBodyAs $ do
                funArgs <- forM (hListToList tconFuncs) (\(Some1 (CoreFunDecl' f)) -> do 
                    tmp <- mkTmpVar (getFunType f) 
                    body <>= [StoreL tmp f]
                    return (Some1 tmp))
                callFunWith "main" funArgs
                body <>= [Halt]
            pure (CoreFunDef startFunDecl funBody)

tctToCoreLang :: TCT.TCT -> CoreMonad (Some2 CoreLang)
tctToCoreLang (TCT.TCT varDecls userFunDecls) = do
    let userFunDecls' = concat userFunDecls

    userFunCtx <- hListFromList <$> mapM funDeclToCoreFunDecl userFunDecls'

    Some1 builtinDefs <- mkBuiltins

    funcs .= liftA2Some (\x y -> Some1 (x +++ y))
                userFunCtx
                (hListMap (Some1 . _funDecl) builtinDefs)

    Some1 globalDecls <- hListFromList <$> mapM varDeclToCoreGlobal varDecls
    Some1 coreGlobals <- pure $ hListMap (\(CoreGlobal v _) -> Some1 v) globalDecls

    Some1 userFunDefs <-
        hListFromList <$> 
            forM userFunDecls' (\(TCT.TCTFunDecl _ (TCT.TCTIdentifier _ id) _ _ tcons funBody) -> do
                vars .= Some1 coreGlobals
                Some1 funDecl <- findFunByName id
                funDeclToCoreInstr funDecl funBody)

    Some1 tconFunDefs <- hListFromList <$> mkTConFuncs

    startFuncDef <- mkStartFun $ hListTCMap (\(CoreFunDef decl _) -> decl) tconFunDefs

    return . Some2 $ CoreLang globalDecls 
                              (builtinDefs +++ tconFunDefs +++ userFunDefs +++ startFuncDef :+: HNil)

performCoreLangGen :: TCT.TCT -> Either Text (Some2 CoreLang)
performCoreLangGen tct = do
    let clState = CoreState (Some1 HNil) (Some1 HNil) [] 1 1
    evalStateT (tctToCoreLang tct) clState
