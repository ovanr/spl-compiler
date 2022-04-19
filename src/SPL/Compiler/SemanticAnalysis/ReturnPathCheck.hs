module SPL.Compiler.SemanticAnalysis.ReturnPathCheck (
    returnPathCheck
    ) where

import qualified Data.Text as T
import SPL.Compiler.Common.Error (definition)

import SPL.Compiler.SemanticAnalysis.TCT
import SPL.Compiler.SemanticAnalysis.TCTEntityLocation


returnPathCheck :: TCT -> TCMonad ()
returnPathCheck (TCT _ funDecls) =
    mapM_ (mapM_ returnPathCheck') funDecls

returnPathCheck' :: TCTFunDecl -> TCMonad ()
returnPathCheck' f@(TCTFunDecl loc (TCTIdentifier _ name) _ t (TCTFunBody _ _ stmts)) = do
    if returnsVoid t || guaranteedReturn' stmts then
        return ()
    else do
        returnTrace <- definition (T.pack "The function '" <> name <> T.pack "' is not guaranteed to return a value.") f
        tcError returnTrace
    where
        returnsVoid :: TCTType -> Bool
        returnsVoid (TCTVoidType _ _) = True
        returnsVoid (TCTFunType _ _ _ t) = returnsVoid t
        returnsVoid _ = False

        guaranteedReturn :: TCTStmt -> Bool
        guaranteedReturn (ReturnStmt _ _) = True 
        guaranteedReturn (IfElseStmt _ _ thenStmts elseStmts) = guaranteedReturn' thenStmts && guaranteedReturn' elseStmts
        guaranteedReturn _ = False

        guaranteedReturn' :: [TCTStmt] -> Bool
        guaranteedReturn' = any guaranteedReturn
