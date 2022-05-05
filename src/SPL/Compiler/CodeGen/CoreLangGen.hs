{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
module SPL.Compiler.CodeGen.CoreLangGen where

import Data.Text (Text)
import qualified Data.Text as T
import Data.Bifunctor
import Control.Lens
import Control.Monad.State
import GHC.Stack
import Control.Applicative

import SPL.Compiler.CodeGen.CoreLang
import SPL.Compiler.CodeGen.CoreLangGenLib
import SPL.Compiler.Common.TypeFunc
import qualified SPL.Compiler.SemanticAnalysis.TCT as TCT
import qualified SPL.Compiler.SemanticAnalysis.TypeCheck as TCT

tctTypeToCoreType :: TCT.TCTType -> Some1 CoreType
tctTypeToCoreType TCT.TCTIntType{} = Some1 CoreIntType
tctTypeToCoreType TCT.TCTBoolType{} = Some1 CoreBoolType
tctTypeToCoreType TCT.TCTCharType{} = Some1 CoreCharType
tctTypeToCoreType TCT.TCTVoidType{} = Some1 CoreVoidType
tctTypeToCoreType TCT.TCTVarType{} = Some1 CoreUnknownType
tctTypeToCoreType (TCT.TCTTupleType _ _ ta tb) =
    case (tctTypeToCoreType ta, tctTypeToCoreType tb) of
        (Some1 ta', Some1 tb') -> Some1 (CoreTupleType ta' tb')
tctTypeToCoreType (TCT.TCTListType _ _ ta) =
    case tctTypeToCoreType ta of
        Some1 ta' -> Some1 (CoreListType ta')
tctTypeToCoreType (TCT.TCTFunType _ _ ta tb) =
    case (tctTypeToCoreType ta, tctTypeToCoreType tb) of
        (Some1 ta', Some1 tb') -> Some1 (CoreFunType ta' tb')


exprToCoreInstr ::TCT.TCTExpr -> CoreMonad (Some1 Var)

exprToCoreInstr (TCT.IntExpr _ i) = do
    tmp <- mkTmpVar CoreIntType
    body <>= [ Declare tmp, StoreI tmp (fromInteger i)]
    pure (Some1 tmp)

exprToCoreInstr (TCT.CharExpr _ c) = do
    tmp <- mkTmpVar CoreCharType
    body <>= [ Declare tmp, StoreC tmp c ]
    pure (Some1 tmp)

exprToCoreInstr (TCT.BoolExpr _ b) = do
    tmp <- mkTmpVar CoreBoolType
    body <>= [ Declare tmp, StoreB tmp b ]
    pure (Some1 tmp)

exprToCoreInstr (TCT.OpExpr _ op e) = do
    someVar1 <- exprToCoreInstr e
    body <>= case (op, someVar1) of
        (TCT.UnNeg, Some1 dst@(Var _ CoreBoolType)) -> [ Not dst dst ]
        (TCT.UnMinus, Some1 dst@(Var _ CoreIntType)) -> [ Neg dst dst ]
        _ -> pureCoreError
    pure someVar1

exprToCoreInstr (TCT.EmptyListExpr _ t) = do
    case tctTypeToCoreType t of
        Some1 t@(CoreListType elemT) -> do 
            tmp <- mkTmpVar t
            body <>= [ Declare tmp, MkNilList tmp ]
            pure (Some1 tmp)
        _ -> coreError

exprToCoreInstr (TCT.TupExpr _ e1 e2) = do
    (Some1 src1@(Var _ ct1)) <- exprToCoreInstr e1
    (Some1 src2@(Var _ ct2)) <- exprToCoreInstr e2
    tmp <- mkTmpVar (CoreTupleType ct1 ct2)
    body <>= [ Declare tmp, MkTup tmp src1 src2]
    pure (Some1 tmp)

exprToCoreInstr (TCT.Op2Expr _ e1 op e2) = do
    case op of
        TCT.Plus -> handleSimpleOp CoreIntType e1 Add e2
        TCT.Minus -> handleSimpleOp CoreIntType e1 Sub e2
        TCT.Mul -> handleSimpleOp CoreIntType e1 Mul e2
        TCT.Div -> handleSimpleOp CoreIntType e1 Div e2
        TCT.Mod -> handleSimpleOp CoreIntType e1 Mod e2
        -- TCT.Pow -> 
        -- TCT.Equal 
        -- TCT.Less 
        -- TCT.Greater 
        -- TCT.LessEq 
        -- TCT.GreaterEq 
        -- TCT.Nequal 
        TCT.Cons -> handleConsOp e1 e2
        TCT.LogAnd -> handleSimpleOp CoreBoolType e1 And e2
        TCT.LogOr -> handleSimpleOp CoreBoolType e1 Or e2
        _ -> lift (Left "Unimplemented")
    where
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
                    body <>= [ Declare tmp', opInstr tmp' src1'' src2' ]
                    return (Some1 tmp')

        handleConsOp :: TCT.TCTExpr ->
                        TCT.TCTExpr ->
                        CoreMonad (Some1 Var)
        handleConsOp e1 e2 = do
            (Some1 elem) <- exprToCoreInstr e1
            (Some1 list@(Var _ lct@(CoreListType _))) <- exprToCoreInstr e2
            whenVarTListEq list elem $ \list' elem' -> do
                tmp <- mkTmpVar lct
                body <>= [Declare tmp, ConsList tmp list' elem']
                return (Some1 tmp)

exprToCoreInstr (TCT.FunCallExpr f) = funCallToCoreInstr f

exprToCoreInstr (TCT.FieldSelectExpr (TCT.TCTFieldSelector _ (TCT.TCTIdentifier _ id) tau fds)) = do
    Some1 src <- findVar id
    funDecl <- mapM (findFun . tctFieldToId) fds
    Some1 dst <- mkFieldSelectorCall src funDecl
    case tctTypeToCoreType tau of
        Some1 concreteRetType -> Some1 <$> unsafeCast dst concreteRetType

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

castFunArg :: Var a -> Var b -> CoreMonad (Var a)
castFunArg arg@(Var _ argT) concreteArg = do
    if hasUnknownType argT then do
        concreteArg' <- mkTmpVar argT
        body <>= [ Declare concreteArg', StoreVUnsafe concreteArg' concreteArg ] 
        pure concreteArg'
    else
        whenVarTEq arg concreteArg $ \arg' concreteArg' -> return concreteArg'

castFunArgs :: HList Var xs -> [Some1 Var] -> CoreMonad (HList Var xs)
castFunArgs HNil [] = pure HNil
castFunArgs (arg :+: args) (Some1 concreteArg:concreteArgs) = do 
    concreteArg' <- castFunArg arg concreteArg
    concreteArgs' <- castFunArgs args concreteArgs
    return (concreteArg' :+: concreteArgs')
castFunArgs _ _ = coreError

funCallToCoreInstr :: TCT.TCTFunCall -> 
                      CoreMonad (Some1 Var)
funCallToCoreInstr (TCT.TCTFunCall _ (TCT.TCTIdentifier _ id) tau args) = do
    argVars <- mapM exprToCoreInstr args
    Some1 (CoreFunDecl' f) <- findFun id
    argVars' <- castFunArgs (f ^. funArgs) argVars
    dst <- mkTmpVar (f ^. funRetType)
    body <>= [Call dst f argVars']
    case tctTypeToCoreType (TCT.getReturnType tau) of
        Some1 concreteRetType -> Some1 <$> unsafeCast dst concreteRetType

fieldSelectorStmtToCoreInstr :: TCT.TCTFieldSelector -> 
                                CoreMonad (Some1 Var)
fieldSelectorStmtToCoreInstr (TCT.TCTFieldSelector _ (TCT.TCTIdentifier _ id) tau fds) = do
    Some1 src <- findVar id
    funDecls <- mapM findFun $ getFunNames fds
    Some1 dst <- case funDecls of
        [] -> Some1 <$> getRef src
        _ -> mkFieldSelectorCall src funDecls
    case tctTypeToCoreType tau of
        Some1 concreteRetType -> Some1 <$> unsafeCast dst concreteRetType

    where
        -- hdAssign :: Ptr [a] -> Ptr a
        -- tlAssign :: Ptr [a] -> Ptr (Ptr [a])
        -- fstAssign :: Ptr (a,b) -> Ptr a
        -- sndAssign :: Ptr (a,b) -> Ptr b
        getFunNames :: [TCT.TCTField] -> [Identifier]
        getFunNames [] = []
        getFunNames [x] = [T.pack (show x) <> "Assign"]
        getFunNames (x:xs) = T.pack (show x) : getFunNames xs


stmtToCoreInstr :: TCT.TCTStmt -> CoreMonad ()

stmtToCoreInstr (TCT.IfElseStmt _ e stmts1 stmts2) = do
    ifElse <- mkLabel "IfElse"
    ifEnd <- mkLabel "IfEnd"
    Some1 cond@(Var _ CoreBoolType) <- exprToCoreInstr e
    body <>= [ BrFalse cond ifElse ]
    mapM_ stmtToCoreInstr stmts1
    body <>= [ BrAlways ifEnd ]
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
            body <>= [ Declare voidVar ]
        Just e -> void $ exprToCoreInstr e

varDeclToCoreGlobal :: TCT.TCTVarDecl -> CoreMonad (Some1 CoreGlobal)
varDeclToCoreGlobal (TCT.TCTVarDecl _ t (TCT.TCTIdentifier _ id) e) =
    case tctTypeToCoreType t of
        Some1 ct -> do
            let dst = Var id ct
            Some1 src <- exprToCoreInstr e
            whenVarTEq dst src $ \dst' src' -> do
                body <>= [Declare dst', StoreV dst' src']
                coreInstr <- use body
                pure . Some1 $ CoreGlobal dst' coreInstr

varDeclToCoreInstr :: TCT.TCTVarDecl -> CoreMonad (Some1 Var)
varDeclToCoreInstr (TCT.TCTVarDecl _ t (TCT.TCTIdentifier _ id) e) =
    case tctTypeToCoreType t of
        Some1 ct -> do
            let dst = Var id ct
            Some1 src <- exprToCoreInstr e
            whenVarTEq dst src $ \dst' src' -> do
                body <>= [Declare dst', StoreV dst' src']
                vars %= (\(Some1 varCtx) -> Some1 $ dst' :+: varCtx)
                pure $ Some1 dst'

mkFunArgs :: [TCT.TCTIdentifier] -> TCT.TCTType -> Some1 (HList Var)
mkFunArgs [] retType = Some1 HNil
mkFunArgs ((TCT.TCTIdentifier _ id):xs) (TCT.TCTFunType _ _ ta tb) = do
    case (tctTypeToCoreType ta, mkFunArgs xs tb) of
        (Some1 cta, Some1 vars) -> Some1 (Var id cta :+: vars)
mkFunArgs _ _ = pureCoreError

funDeclToCoreInstr :: TCT.TCTFunDecl ->
                      CoreMonad (Some1 CoreFunDef)
funDeclToCoreInstr (TCT.TCTFunDecl _ (TCT.TCTIdentifier _ id) args tau (TCT.TCTFunBody _ varDecls stmts)) = do
    case (mkFunArgs args tau, tctTypeToCoreType (TCT.getReturnType tau)) of
        (Some1 argVars, Some1 retType) -> do
            vars %= \(Some1 varCtx) -> Some1 (argVars +++ varCtx)
            Some1 localVars <- hListFromList <$> mapM varDeclToCoreInstr varDecls
            mapM_ stmtToCoreInstr stmts
            funBody <- use body
            return . Some1 $ CoreFunDef (CoreFunDecl' (CoreFunDecl id argVars localVars retType)) funBody

mkFunCtx :: [TCT.TCTFunDecl] -> Some1 (HList CoreFunDecl')
mkFunCtx [] = Some1 HNil
mkFunCtx ((TCT.TCTFunDecl _ (TCT.TCTIdentifier _ id) args tau _):xs) = do
    case (mkFunArgs args tau, tctTypeToCoreType (TCT.getReturnType tau), mkFunCtx xs) of
        (Some1 argVars, Some1 retType, Some1 funCtx') -> 
            Some1 $ CoreFunDecl' (CoreFunDecl id argVars HNil retType) :+: funCtx'

tctToCoreLang :: TCT.TCT -> CoreMonad (Some2 CoreLang)
tctToCoreLang (TCT.TCT varDecls funDecls) = do 
    let funDecls' = concat funDecls
        funCtx = mkFunCtx funDecls' 
    funcs .= funCtx

    Some1 globalDecls <- hListFromList <$> mapM varDeclToCoreGlobal varDecls
    Some1 coreGlobals <- pure $ hListMap (\(CoreGlobal v _) -> Some1 v) globalDecls
    Some1 funDefs <- 
        hListFromList <$> forM funDecls' (\f -> do
            vars .= Some1 coreGlobals
            body .= []
            funDeclToCoreInstr f)

    return . Some2 $ CoreLang globalDecls funDefs
