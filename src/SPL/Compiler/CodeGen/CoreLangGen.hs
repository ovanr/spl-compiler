{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
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
import SPL.Compiler.Common.TypeFunc
import qualified SPL.Compiler.SemanticAnalysis.TCT as TCT
import qualified SPL.Compiler.SemanticAnalysis.TypeCheck.TCon as TCT
import qualified SPL.Compiler.SemanticAnalysis.TypeCheck as TCT

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

exprToCoreInstr e@(TCT.Op2Expr loc e1 op e2) = do
    case op of
        TCT.Plus -> handleSimpleOp CoreIntType e1 Add e2
        TCT.Minus -> handleSimpleOp CoreIntType e1 Sub e2
        TCT.Mul -> handleSimpleOp CoreIntType e1 Mul e2
        TCT.Div -> handleSimpleOp CoreIntType e1 Div e2
        TCT.Mod -> handleSimpleOp CoreIntType e1 Mod e2
        TCT.Pow -> lift (Left "Core functionality unimplemented")
        TCT.Equal -> handleOverloadedOp (T.isPrefixOf "'eq_con") e1 e2
        TCT.Less  -> handleOverloadedOp (T.isPrefixOf "'ord_con") e1 e2
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
            body <>= [ Declare dst, CallV dst solver (src1 :+: src2 :+: HNil) ]
            return $ Some1 dst

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
    Some1 src <- findVarByName id
    funDecl <- mapM (findFun . tctFieldToId) fds
    Some1 dst@(Var _ dstT) <- mkFieldSelectorCall src funDecl
    if hasUnknownType dstT then
        case tctTypeToCoreType tau of
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
castFunArgs hs ys = coreErrorWithDesc . T.pack $
    "Mismatched number of function arguments: " <>
    show (hListLength hs) <> " /= " <> show (length ys)

funCallToCoreInstr :: TCT.TCTFunCall -> CoreMonad (Some1 Var)
funCallToCoreInstr (TCT.TCTFunCall _ (TCT.TCTIdentifier _ "print") _ args) = do
    [Some1 arg@(Var _ argT)] <- mapM exprToCoreInstr args
    let printType = CoreFunType (argT :+: HNil) CoreVoidType
    conVar <- findVar (T.isPrefixOf "'print_con") printType
    dst <- mkTmpVar CoreVoidType
    body <>= [Declare dst, CallV dst conVar (arg :+: HNil)]
    return (Some1 dst)

funCallToCoreInstr (TCT.TCTFunCall _ (TCT.TCTIdentifier _ id) tau args) = do
    argVars <- mapM exprToCoreInstr args
    Some1 (CoreFunDecl' f) <- findFun id
    conVars <- mapM findConVar (S.toList $ TCT.getTypeCon tau) 
    argVars' <- castFunArgs (f ^. funArgs) (conVars ++ argVars)
    dst <- mkTmpVar (f ^. funRetType)
    body <>= [Declare dst, Call dst f argVars']
    case tctTypeToCoreType (TCT.getReturnType tau) of
        Some1 concreteRetType -> Some1 <$> unsafeCast dst concreteRetType

fieldSelectorStmtToCoreInstr :: TCT.TCTFieldSelector ->
                                CoreMonad (Some1 Var)
fieldSelectorStmtToCoreInstr (TCT.TCTFieldSelector _ (TCT.TCTIdentifier _ id) tau fds) = do
    Some1 src <- findVarByName id
    funDecls <- mapM findFun $ getFunNames fds
    Some1 dst <- case funDecls of
        [] -> Some1 <$> getRef src
        _ -> mkFieldSelectorCall src funDecls
    case tctTypeToCoreType tau of
        Some1 concreteRetType -> Some1 <$> unsafeCast dst concreteRetType

    where
        getFunNames :: [TCT.TCTField] -> [Identifier]
        getFunNames [] = []
        getFunNames [x] = [T.pack (show x) <> "_assign"]
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
            body <>= [ Declare voidVar, RetV voidVar ]
        Just e -> do
            (Some1 dst) <- exprToCoreInstr e
            body <>= [RetV dst]

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
mkFunArgs ((TCT.TCTIdentifier _ id):xs) (TCT.TCTFunType _ _ ta tb) = do
    case (tctTypeToCoreType ta, mkFunArgs xs tb) of
        (Some1 cta, Some1 vars) -> Some1 (Var id cta :+: vars)
mkFunArgs _ _ = pureCoreError

funDeclToCoreFunDecl :: TCT.TCTFunDecl -> CoreMonad (Some1 CoreFunDecl')
funDeclToCoreFunDecl (TCT.TCTFunDecl _ (TCT.TCTIdentifier _ id) args tau _) = do
    Some1 conVars <- mkTConArgs (S.toList $ TCT.getTypeCon tau)
    
    case (mkFunArgs args tau, tctTypeToCoreType (TCT.getReturnType tau)) of
        (Some1 argVars, Some1 retType) -> do
            return . Some1 . CoreFunDecl' $ CoreFunDecl id (conVars +++ argVars) retType

funDeclToCoreInstr :: CoreFunDecl' xs -> TCT.TCTFunBody -> CoreMonad (Some1 CoreFunDef)
funDeclToCoreInstr decl@(CoreFunDecl' (CoreFunDecl _ args _)) (TCT.TCTFunBody _ varDecls stmts) = do
    vars %= \(Some1 varCtx) -> Some1 (args +++ varCtx)
    mapM_ varDeclToCoreInstr varDecls
    mapM_ stmtToCoreInstr stmts
    funBody <- use body
    return . Some1 $ CoreFunDef decl funBody

mkMagicFuncs :: Some1 (HList CoreFunDef)
mkMagicFuncs = Some1 $ isEmpty :+: hd :+: tl :+: fst :+: snd :+: HNil
    where
        mkMagicFun :: Identifier -> HList Var xs -> CoreType r -> CoreFunDef (Snoc xs r)
        mkMagicFun id args retType = CoreFunDef (CoreFunDecl' (CoreFunDecl id args retType)) [Halt]

        isEmpty :: CoreFunDef '[Ptr [Unknown], Bool]
        isEmpty = mkMagicFun "isEmpty" (Var "x" (CoreListType (CoreUnknownType "a")) :+: HNil) CoreBoolType

        hd :: CoreFunDef '[Ptr [Unknown], Unknown]
        hd = mkMagicFun "hd" (Var "x" (CoreListType (CoreUnknownType "a")) :+: HNil) (CoreUnknownType "a")

        tl :: CoreFunDef '[Ptr [Unknown], Ptr [Unknown]]
        tl = mkMagicFun "tl" (Var "x" (CoreListType (CoreUnknownType "a")) :+: HNil) (CoreListType (CoreUnknownType "a"))

        fst :: CoreFunDef '[Ptr (Unknown, Unknown), Unknown]
        fst = mkMagicFun "fst" (Var "x" (CoreTupleType (CoreUnknownType "a") (CoreUnknownType "b")) :+: HNil) (CoreUnknownType "a")

        snd :: CoreFunDef '[Ptr (Unknown, Unknown), Unknown]
        snd = mkMagicFun "snd" (Var "x" (CoreTupleType (CoreUnknownType "a") (CoreUnknownType "b")) :+: HNil) (CoreUnknownType "b")

        hdAssign :: CoreFunDef '[Ptr [Unknown], Ptr Unknown]
        hdAssign = mkMagicFun "hd_assign"
                        (Var "x" (CoreListType (CoreUnknownType "a")) :+: HNil)
                        (CorePtrType (CoreUnknownType "a"))

        tlAssign :: CoreFunDef '[Ptr [Unknown], Ptr (Ptr [Unknown])]
        tlAssign = mkMagicFun "tl_assign"
                        (Var "x" (CoreListType (CoreUnknownType "a")) :+: HNil)
                        (CorePtrType $ CoreListType (CoreUnknownType "a"))

        fstAssign :: CoreFunDef '[Ptr (Unknown, Unknown), Ptr Unknown]
        fstAssign = mkMagicFun "fst_assign"
                        (Var "x" (CoreTupleType (CoreUnknownType "a") (CoreUnknownType "b")) :+: HNil)
                        (CorePtrType (CoreUnknownType "a"))

        sndAssign :: CoreFunDef '[Ptr (Unknown, Unknown), Ptr Unknown]
        sndAssign = mkMagicFun "snd_assign"
                        (Var "x" (CoreTupleType (CoreUnknownType "a") (CoreUnknownType "b")) :+: HNil)
                        (CorePtrType (CoreUnknownType "b"))

tctToCoreLang :: TCT.TCT -> CoreMonad (Some2 CoreLang)
tctToCoreLang (TCT.TCT varDecls funDecls) = do
    let funDecls' = concat funDecls
        magicFuncs = mkMagicFuncs

    funCtx <- hListFromList <$> mapM funDeclToCoreFunDecl funDecls'

    funcs .= liftA2Some (\x y -> Some1 (x +++ y))
                funCtx
                (withSome1 magicFuncs $ hListMap (Some1 . _funDecl))

    Some1 globalDecls <- hListFromList <$> mapM varDeclToCoreGlobal varDecls
    Some1 coreGlobals <- pure $ hListMap (\(CoreGlobal v _) -> Some1 v) globalDecls
    Some1 funDefs <-
        liftA2Some (\x y -> Some1 (x +++ y)) magicFuncs . hListFromList
            <$> forM funDecls' (\(TCT.TCTFunDecl _ (TCT.TCTIdentifier _ id) _ _ funBody) -> do
                vars .= Some1 coreGlobals
                Some1 funDecl <- findFun id
                body .= []
                funDeclToCoreInstr funDecl funBody)

    return . Some2 $ CoreLang globalDecls funDefs
