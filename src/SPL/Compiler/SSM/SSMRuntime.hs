{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ExtendedDefaultRules #-}

module SPL.Compiler.SSM.SSMRuntime where

import Data.Text (Text)
import SPL.Compiler.SSM.SSMGenLib
import qualified SPL.Compiler.SSM.SSMGenLib as SSM

default (Int, Text) 

genPowFun = do
    newBlock "_pow"
    end <- newLabel "end"
    loop <- newLabel "loop"
    exception <- newLabel "exception"
    SSM.link 2
    SSM.ldl (-3)
    SSM.stl 2
    SSM.ldc 1
    SSM.stl 1
    newBlock loop
    SSM.ldl (-2)
    SSM.ldc 0
    SSM.lt
    SSM.brt exception
    SSM.ldl (-2)
    SSM.ldc 0
    SSM.le
    SSM.brt end
    SSM.ldl 1
    SSM.ldl 2
    SSM.mul
    SSM.stl 1
    SSM.ldl (-2)
    SSM.ldc 1
    SSM.sub
    SSM.stl (-2)
    SSM.bra loop
    newBlock end
    SSM.ldl 1
    SSM.str RR
    removeStackFrame
    newBlock exception
    SSM.printString "\n**Exception: negative exponent**"
    SSM.halt
    
genEq = do
    newBlock "_eq_int"
    newBlock "_eq_bool"
    newBlock "_eq_char"
    SSM.link 0
    SSM.ldl (-3)
    SSM.ldl (-2)
    SSM.eq
    SSM.str RR
    removeStackFrame

genTrueVoid = do
    newBlock "_eq_void"
    newBlock "_le_void"
    newBlock "_ge_void"
    SSM.link 0
    ldc True
    SSM.str RR
    removeStackFrame

genListCombinator = do
    startLoop <- newLabel "loop_start" 
    success <- newLabel "success" 
    failure <- newLabel "failure" 
    newBlock "_eq_list"
    newBlock "_lt_list"
    newBlock "_le_list"
    newBlock "_gt_list"
    newBlock "_ge_list"
    SSM.link 0
    newBlock startLoop
    SSM.ldl (-4)
    SSM.ldl (-3)
    SSM.eq
    SSM.brt success
    SSM.ldc 0
    SSM.ldl (-4)
    SSM.eq
    SSM.brt failure
    SSM.ldc 0
    SSM.ldl (-3)
    SSM.eq
    SSM.brt failure
    SSM.ldl (-4) 
    SSM.lda (-1) 
    SSM.ldl (-3) 
    SSM.lda (-1)
    SSM.ldc 2
    SSM.ldl (-2)
    SSM.bsr "__call_thunk"
    SSM.ajs (-4)
    SSM.ldr RR
    SSM.brf failure
    SSM.ldl (-4)
    SSM.lda 0
    SSM.stl (-4)
    SSM.ldl (-3)
    SSM.lda 0
    SSM.stl (-3)
    SSM.bra startLoop
    newBlock failure
    ldc False
    SSM.str RR
    removeStackFrame
    newBlock success
    ldc True
    SSM.str RR
    removeStackFrame

genTupCombinator = do 
    failure <- newLabel "failure"
    newBlock "_eq_tup"
    newBlock "_lt_tup"
    newBlock "_le_tup"
    newBlock "_gt_tup"
    newBlock "_ge_tup"
    SSM.link 0
    SSM.ldl (-5)
    SSM.lda 0
    SSM.ldl (-4)
    SSM.lda 0
    SSM.ldc 2
    SSM.ldl (-2)
    SSM.bsr "__call_thunk"
    SSM.ajs (-4)
    SSM.ldr RR
    SSM.brf failure
    SSM.ldl (-5)
    SSM.lda (-1)
    SSM.ldl (-4)
    SSM.lda (-1)
    SSM.ldc 2
    SSM.ldl (-3)
    SSM.bsr "__call_thunk"
    SSM.ajs (-4)
    SSM.ldr RR
    SSM.brf failure
    ldc True
    SSM.str RR
    removeStackFrame
    newBlock failure
    ldc False
    SSM.str RR
    removeStackFrame

genLt = do
    newBlock "_lt_int"
    newBlock "_lt_bool"
    newBlock "_lt_char"
    SSM.link 0
    SSM.ldl (-2)
    SSM.ldl (-3)
    SSM.lt
    SSM.str RR
    removeStackFrame

genFalseVoid = do
    newBlock "_lt_void"
    newBlock "_gt_void"
    SSM.link 0
    ldc False
    SSM.str RR
    removeStackFrame

genLe = do
    newBlock "_le_int"
    newBlock "_le_bool"
    newBlock "_le_char"
    SSM.link 0
    SSM.ldl (-2)
    SSM.ldl (-3)
    SSM.le
    SSM.str RR
    removeStackFrame

genGt = do
    newBlock "_gt_int"
    newBlock "_gt_bool"
    newBlock "_gt_char"
    SSM.link 0
    SSM.ldl (-2)
    SSM.ldl (-3)
    SSM.gt
    SSM.str RR
    removeStackFrame

genGe = do
    newBlock "_ge_int"
    newBlock "_ge_bool"
    newBlock "_ge_char"
    SSM.link 0
    SSM.ldl (-2)
    SSM.ldl (-3)
    SSM.ge
    SSM.str RR
    removeStackFrame

genIsEmpty = do
    newBlock "isEmpty"
    SSM.link 0
    SSM.ldl (-2)
    SSM.ldc 0
    SSM.eq
    SSM.str RR
    removeStackFrame

genHd = do
    newBlock "hd"
    SSM.link 0
    SSM.ldl (-2)
    SSM.ldc 0       -- check for null pointer -> empty list
    SSM.eq
    SSM.brt "__get_hd_exception"
    SSM.ldl (-2)
    SSM.lda (-1)
    SSM.str RR
    removeStackFrame

genTl = do
    newBlock "tl"
    SSM.link 0
    SSM.ldl (-2)
    SSM.ldc 0       -- check for null pointer -> empty list
    SSM.eq
    SSM.brt "__get_tl_exception"
    SSM.ldl (-2)
    SSM.lda 0
    SSM.str RR
    removeStackFrame

genFst = do
    newBlock "fst"
    SSM.link 0
    SSM.ldl (-2)
    SSM.lda 0
    SSM.str RR
    removeStackFrame

genSnd = do
    newBlock "snd"
    SSM.link 0
    SSM.ldl (-2)
    SSM.lda (-1)
    SSM.str RR
    removeStackFrame

genPrint = do
    newBlock "print"
    SSM.link 0
    SSM.ldl (-3)
    SSM.ldc 1
    SSM.ldl (-2)
    SSM.bsr "__call_thunk"
    removeStackFrame

genPrintInt = do
    newBlock "_print_int"
    SSM.link 0
    SSM.ldl (-2)
    SSM.trap 0
    removeStackFrame

genPrintChar = do
    newBlock "_print_char"
    SSM.link 0
    SSM.ldl (-2)
    SSM.trap 1
    removeStackFrame

genPrintCharList = do
    newBlock "_print_char_list"
    end <- newLabel "end"
    loop <- newLabel "loop"
    SSM.link 0
    SSM.printChar '"'
    newBlock loop
    SSM.ldl (-2)
    SSM.ldc 0
    SSM.eq
    SSM.brt end
    SSM.ldl (-2)
    SSM.lda (-1)
    SSM.trap 1
    SSM.ldl (-2)    
    SSM.lda 0
    SSM.stl (-2)
    SSM.bra loop
    newBlock end
    SSM.printChar '"'
    removeStackFrame

genPrintBool = do
    branchFalse <- newLabel "false" 
    newBlock "_print_bool"
    SSM.link 0
    SSM.ldl (-2)
    SSM.brf branchFalse
    SSM.printString "True"
    removeStackFrame
    newBlock branchFalse
    SSM.printString "False"
    removeStackFrame

genPrintVoid = do
    newBlock "_print_void"
    SSM.printString "Void"
    removeStackFrame

genPrintList = do
    end <- newLabel "end"
    loop <- newLabel "loop"
    newBlock "_print_list"
    SSM.link 0
    SSM.printChar '['
    SSM.ldl (-3)    -- load pointer to fst list node
    SSM.ldc 0       -- check for null pointer
    SSM.eq
    SSM.brt end     -- print first element without prepended comma
    SSM.ldl (-3)    -- load list ptr
    SSM.lda (-1)    -- get element of list node
    SSM.ldc 1
    SSM.ldl (-2)    -- load print fun
    SSM.bsr "__call_thunk"
    SSM.ajs (-3)
    SSM.ldl (-3)    -- load pointer to first list node
    SSM.lda 0       -- load pointer to next list node
    newBlock loop   -- expects pointer to next list node on top of stack
    SSM.lds 0
    SSM.lds 0
    SSM.ldc 0       -- check for null pointer
    SSM.eq
    SSM.brt end
    SSM.printChar ','
    SSM.lda (-1)    -- get element of list node
    SSM.ldc 1
    SSM.ldl (-2)    -- load print fun
    SSM.bsr "__call_thunk"         -- call print fun
    SSM.ajs (-3)
    SSM.lda 0
    SSM.bra loop
    newBlock end
    SSM.printChar ']'
    removeStackFrame

genPrintTup = do 
    failure <- newLabel "failure"
    newBlock "_print_tup"
    SSM.link 0
    SSM.printChar '('
    SSM.ldl (-4)
    SSM.lda 0
    SSM.ldc 1
    SSM.ldl (-2)
    SSM.bsr "__call_thunk"
    SSM.ajs (-3)
    SSM.printChar ','
    SSM.ldl (-4)
    SSM.lda (-1)
    SSM.ldc 1
    SSM.ldl (-3)
    SSM.bsr "__call_thunk"
    SSM.ajs (-3)
    SSM.printChar ')'
    SSM.str RR
    removeStackFrame

-- arg1
-- expected args
-- actual args
genStoreThunkFun :: SSMMonad ()
genStoreThunkFun = do
    newBlock "__store_thunk"
    SSM.link 1 
    SSM.ldl (-2) -- load first arg = actual num of arguments passed to thunk
    SSM.ldc 4 
    SSM.add 
    SSM.stl 1 -- local variable stores offset from MP to the head of the thunk
    SSM.ldc 0
    newBlock "__store_thunk_loop"
    SSM.ldl 1
    SSM.ldc 1
    SSM.eq
    SSM.brt "__end_store_thunk"
    SSM.ajs (-1)
    SSM.ldr MP
    SSM.ldl 1
    SSM.sub
    SSM.lda 0
    SSM.sth
    SSM.ldl 1
    SSM.ldc 1
    SSM.sub
    SSM.stl 1
    SSM.bra "__store_thunk_loop"
    newBlock "__end_store_thunk"
    SSM.str RR
    removeStackFrame

-- arg2 (mp -5)
-- arg1 (mp -4)
-- num args passed (e.g. 2) (mp -3)
-- thunk location (mp -2)
-- ret addr
-- mp
genCallThunkFun :: SSMMonad ()
genCallThunkFun = do
    newBlock "__call_thunk"
    SSM.link 1 -- local counter `c`
    SSM.ldl (-3) -- number of new arguments given to the existing thunk, `nargs`
    SSM.stl 1 -- c = num args passed
    newBlock "__load_args_loop"
    SSM.ldl 1
    SSM.ldc 1
    SSM.ge -- c >= 1
    SSM.brf "__load_thunk"
    -- here c >= 1
    SSM.ldr MP
    SSM.ldl 1
    SSM.sub -- sp: mp - c
    SSM.lda (-3) -- sp = *(mp - c - 3)
    SSM.ldl 1 -- sp: c
    SSM.ldc 1 -- sp: 1
    SSM.sub -- sp: c - 1
    SSM.stl 1 -- c = c - 1
    SSM.bra "__load_args_loop"
    newBlock "__load_thunk"
    -- here c == 0
    -- stack contains arguments
    -- arg2
    -- arg1
    SSM.ldl (-2) -- thunk
    SSM.lda 0 -- load thunk
    SSM.ldc 3
    SSM.add 
    SSM.stl 1 -- c = 3 + num args present already in thunk
    newBlock "__load_thunk_loop"
    SSM.ldl 1 -- load c
    SSM.ldc 1
    SSM.ge -- is c >= 1
    SSM.brf "__eval_thunk"
    -- c >= 1
    SSM.ldl (-2) -- thunk location
    SSM.ldl 1 -- c
    SSM.sub -- sp: thunk location - c
    SSM.lda 1 -- load topmost thunk argument
    SSM.ldl 1
    SSM.ldc 1
    SSM.sub 
    SSM.stl 1 -- c = c - 1
    SSM.bra "__load_thunk_loop"
    newBlock "__eval_thunk"
    -- at this point appended version of thunk is in stack
    SSM.ldl (-3)
    SSM.add -- adjust number of given arguments in thunk 
    SSM.lds (-1) -- num args thunk takes
    SSM.lds (-1) -- num args given to thunk
    SSM.eq 
    SSM.brt "__eval_saturated_thunk"
    SSM.lds (-1) -- num args thunk takes
    SSM.lds (-1) -- num args given to thunk
    SSM.lt 
    SSM.brt "__eval_nested_saturated_thunk"
    SSM.bsr "__store_thunk"
    removeStackFrame
    newBlock "__eval_saturated_thunk"
    SSM.ajs (-2)
    SSM.jsr
    removeStackFrame
    newBlock "__eval_nested_saturated_thunk"
    SSM.swp
    SSM.sub
    SSM.stl 1
    SSM.jsr
    SSM.ldl (-2) -- thunk
    SSM.lda (-1) -- num args the previous thunk took (var `m`)
    SSM.stl (-2) -- thunk location arg now stores our counter `m`
    newBlock "__pop_prev_args"
    SSM.ldl (-2)
    SSM.ldc 0
    SSM.eq
    SSM.brt "__call_nested_thunk"
    SSM.ajs (-1)
    SSM.ldl (-2)
    SSM.ldc 1
    SSM.sub
    SSM.stl (-2)
    SSM.bra "__pop_prev_args"
    newBlock "__call_nested_thunk"
    SSM.ldl 1 -- load num new args
    SSM.ldr RR
    SSM.bsr "__call_thunk"
    removeStackFrame

genAssignTailEmptyListException = do
    newBlock "__assign_tl_exception"
    SSM.printString "**Exception: Cannot assign to tail of empty list!**"
    SSM.halt

genAssignHeadEmptyListException = do
    newBlock "__assign_hd_exception"
    SSM.printString "**Exception: Cannot assign to head of empty list!**"
    SSM.halt

genGetHeadEmptyListException = do
    newBlock "__get_hd_exception"
    SSM.printString "**Exception: Cannot get head of empty list!**"
    SSM.halt

genGetTailEmptyListException = do
    newBlock "__get_tl_exception"
    SSM.printString "**Exception: Cannot get tail of empty list!**"
    SSM.halt

mkRuntimeSystem :: SSMMonad ()
mkRuntimeSystem = 
    let actions = [genPowFun,
                   genEq,
                   genTrueVoid,
                   genFalseVoid,
                   genListCombinator,
                   genTupCombinator,
                   genLt,
                   genLe,
                   genGt,
                   genGe,
                   genPrintInt,
                   genPrintBool,
                   genPrintChar,
                   genPrintVoid,
                   genPrintList,
                   genPrintCharList,
                   genPrintTup,
                   genIsEmpty,
                   genHd,
                   genTl,
                   genFst,
                   genSnd,
                   genPrint,
                   genCallThunkFun,
                   genStoreThunkFun,
                   genGetHeadEmptyListException,
                   genGetTailEmptyListException,
                   genAssignHeadEmptyListException,
                   genAssignTailEmptyListException] 
    in sequence_ actions
