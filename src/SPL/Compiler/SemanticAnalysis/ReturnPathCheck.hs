module SPL.Compiler.SemanticAnalysis.ReturnPathCheck (
    returnPathCheck
    ) where

import qualified Data.Text as T
import SPL.Compiler.Common.Error (definition, throwErr)

import SPL.Compiler.SemanticAnalysis.Core
import SPL.Compiler.SemanticAnalysis.CoreEntityLocation
import Data.Graph

returnPathCheck :: Core -> TCMonad ()
returnPathCheck (Core _ funDecls) =
    mapM_ (mapM_ returnPathCheck'. unSCC) funDecls
    where
        unSCC (AcyclicSCC x) = [x]
        unSCC (CyclicSCC xs) = xs

returnPathCheck' :: CoreFunDecl -> TCMonad ()
returnPathCheck' f@(CoreFunDecl loc (CoreIdentifier _ name) _ t (CoreFunBody _ _ stmts)) = do
    if returnsVoid t || guaranteedReturn' stmts then
        return ()
    else do
        returnTrace <- definition (T.pack "The function '" <> name <> T.pack "' is not guaranteed to return a value.") f
        throwErr returnTrace
    where
        returnsVoid :: CoreType -> Bool
        returnsVoid (CoreVoidType _) = True
        returnsVoid (CoreFunType _ _ t) = returnsVoid t
        returnsVoid _ = False

        guaranteedReturn :: CoreStmt -> Bool
        guaranteedReturn (ReturnStmt _ _) = True 
        guaranteedReturn (WhileStmt _ (BoolExpr _ True) _) = True 
        guaranteedReturn (IfElseStmt _ _ thenStmts elseStmts) = guaranteedReturn' thenStmts && guaranteedReturn' elseStmts
        guaranteedReturn _ = False

        guaranteedReturn' :: [CoreStmt] -> Bool
        guaranteedReturn' = any guaranteedReturn

