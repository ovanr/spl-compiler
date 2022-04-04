module SPL.Compiler.TypeChecker.TreeTransformer where

import qualified SPL.Compiler.Parser.AST as AST
import SPL.Compiler.TypeChecker.TCT
import qualified SPL.Compiler.Lexer.AlexLexGen as AST

ast2tct :: AST.AST -> TCT
ast2tct (AST.AST leaves) = TCT $ map ast2tctLeaf leaves

ast2tctLeaf :: AST.ASTLeaf -> TCTLeaf
ast2tctLeaf (AST.ASTVar varDecl) = TCTVar (ast2tctVarDecl varDecl)
ast2tctLeaf (AST.ASTFun funDecl) = TCTFun (ast2tctFunDecl funDecl)

ast2tctVarDecl :: AST.ASTVarDecl -> TCTVarDecl
ast2tctVarDecl (AST.ASTVarDecl loc t id expr) = TCTVarDecl loc (ast2tctType t) (ast2tctId id) (ast2tctExpr expr)

ast2tctFunDecl :: AST.ASTFunDecl -> TCTFunDecl 
ast2tctFunDecl (AST.ASTFunDecl loc id args t body) = TCTFunDecl loc (ast2tctId id) (map ast2tctId args) (ast2tctType t) (ast2tctFunBody body)

ast2tctFunBody :: AST.ASTFunBody -> TCTFunBody 
ast2tctFunBody (AST.ASTFunBody loc varDecls stmts) = TCTFunBody loc (map ast2tctVarDecl varDecls) (map ast2tctStmt stmts)

ast2tctStmt :: AST.ASTStmt -> TCTStmt 
ast2tctStmt (AST.IfElseStmt loc expr thenStmts elseStmts) =
    IfElseStmt loc (ast2tctExpr expr) (map ast2tctStmt thenStmts) (map ast2tctStmt elseStmts)
ast2tctStmt (AST.WhileStmt loc expr stmts) = WhileStmt loc (ast2tctExpr expr) (map ast2tctStmt stmts)
ast2tctStmt (AST.AssignStmt loc fldSlct expr) = AssignStmt loc (ast2tctFldSlct fldSlct) (ast2tctExpr expr)
ast2tctStmt (AST.FunCallStmt loc funCall) = FunCallStmt loc (ast2tctFunCall funCall)
ast2tctStmt (AST.ReturnStmt loc Nothing) = ReturnStmt loc Nothing
ast2tctStmt (AST.ReturnStmt loc (Just expr)) = ReturnStmt loc (Just (ast2tctExpr expr))


ast2tctFunCall :: AST.ASTFunCall -> TCTFunCall 
ast2tctFunCall (AST.ASTFunCall loc id exprs) = TCTFunCall loc (ast2tctId id) (map ast2tctExpr exprs)

ast2tctFldSlct :: AST.ASTFieldSelector -> TCTFieldSelector 
ast2tctFldSlct (AST.ASTFieldSelector loc id fields) = TCTFieldSelector loc (ast2tctId id) (map ast2tctFld fields)

ast2tctFld :: AST.ASTField -> TCTField 
ast2tctFld (AST.Hd loc) = Hd loc
ast2tctFld (AST.Tl loc) = Tl loc
ast2tctFld (AST.Fst loc) = Fst loc
ast2tctFld (AST.Snd loc) = Snd loc

ast2tctId :: AST.ASTIdentifier -> TCTIdentifier
ast2tctId (AST.ASTIdentifier loc t) = TCTIdentifier loc t

ast2tctExpr :: AST.ASTExpr -> TCTExpr
ast2tctExpr = undefined

ast2tctType :: AST.ASTType -> TCTType 
ast2tctType (AST.ASTUnknownType loc) = TCTVarType loc mempty
ast2tctType (AST.ASTFunType loc ts) = typeFold loc $ map ast2tctType ts
    where
        typeFold :: AST.EntityLoc -> [TCTType] -> TCTType
        typeFold loc [] = error "unexpected"
        typeFold loc [t] = t
        typeFold loc (t:ts) = TCTFunType loc [] t (typeFold loc ts)
ast2tctType (AST.ASTTupleType loc tl tr) = TCTTupleType loc (ast2tctType tl) (ast2tctType tr)
ast2tctType (AST.ASTListType loc t) = TCTListType loc (ast2tctType t)
ast2tctType (AST.ASTVarType loc t) = TCTVarType loc t
ast2tctType (AST.ASTIntType loc) = TCTIntType loc
ast2tctType (AST.ASTBoolType loc) = TCTBoolType loc
ast2tctType (AST.ASTCharType loc) = TCTCharType loc
ast2tctType (AST.ASTVoidType loc) = TCTVoidType loc


