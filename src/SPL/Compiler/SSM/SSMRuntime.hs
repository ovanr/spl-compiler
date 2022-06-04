{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ExtendedDefaultRules #-}

module SPL.Compiler.SSM.SSMRuntime where

import Data.Text (Text)
import SPL.Compiler.SSM.SSMGenLib
import qualified SPL.Compiler.SSM.SSMGenLib as SSM

default (Int, Text) 

genEqInt = do
    newBlock "_eq_int"
    SSM.link 0
    SSM.ldl (-3)
    SSM.ldl (-2)
    SSM.eq
    SSM.str RR
    removeStackFrame

genEqBool = do
    newBlock "_eq_bool"
    SSM.link 0
    SSM.ldl (-3)
    SSM.ldl (-2)
    SSM.eq
    SSM.str RR
    removeStackFrame

genEqChar = do
    newBlock "_eq_char"
    SSM.link 0
    SSM.ldl (-3)
    SSM.ldl (-2)
    SSM.eq
    SSM.str RR
    removeStackFrame

genEqVoid = do
    newBlock "_eq_void"
    SSM.link 0
    ldc True
    SSM.str RR
    removeStackFrame

genEqOrdList = do
    startLoop <- newLabel "loop_start" 
    success <- newLabel "success" 
    failure <- newLabel "failure" 
    newBlock "_eq_list"
    newBlock "_ord_list"
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
    SSM.lda (-4)
    SSM.stl (-4)
    SSM.lda (-3)
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

genEqOrdTup = do 
    failure <- newLabel "failure"
    newBlock "_eq_tup"
    newBlock "_ord_tup"
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

genOrdInt = do
    newBlock "_ord_int"
    SSM.link 0
    SSM.ldl (-3)
    SSM.ldl (-2)
    SSM.lt
    SSM.str RR
    removeStackFrame

genOrdBool = do
    newBlock "_ord_bool"
    SSM.link 0
    SSM.ldl (-2)
    SSM.not
    SSM.ldl (-3)
    SSM.and
    SSM.str RR
    removeStackFrame

genOrdChar = do
    newBlock "_ord_char"
    SSM.link 0
    SSM.ldl (-3)
    SSM.ldl (-2)
    SSM.lt
    SSM.str RR
    removeStackFrame

genOrdVoid = do
    newBlock "_ord_void"
    SSM.link 0
    ldc False
    SSM.str RR
    removeStackFrame

genHd = do
    newBlock "hd"
    SSM.link 0
    SSM.ldl (-2)
    SSM.lda (-1)
    SSM.str RR
    removeStackFrame

genTl = do
    newBlock "tl"
    SSM.link 0
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
    SSM.ldl (-3)    -- load pointer to next list node
    SSM.lda 0     
    newBlock loop   -- expects pointer to next list node on top of stack
    SSM.ldc 0       -- check for null pointer
    SSM.eq
    SSM.brt end
    SSM.printChar ','
    SSM.ldl (-3)    -- load list ptr
    SSM.lda (-1)    -- get element of list node
    SSM.ldl (-2)    -- load print fun
    SSM.jsr         -- call print fun
    SSM.ldl (-3)    -- load pointer to next list node
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

genCallThunkFun :: SSMMonad ()
genCallThunkFun = do
    newBlock "__call_thunk"
    SSM.link 1
    SSM.ldl (-3) -- number of new arguments given to the existing thunk
    SSM.stl 1 
    newBlock "__load_args_loop"
    SSM.ldl 1
    SSM.ldc 1
    SSM.ge
    SSM.brf "__load_thunk"
    SSM.ldr MP 
    SSM.ldl 1
    SSM.sub 
    SSM.lda (-3)
    SSM.ldl 1
    SSM.ldc 1
    SSM.sub 
    SSM.stl 1
    SSM.bra "__load_args_loop"
    newBlock "__load_thunk"
    SSM.ldl (-2)
    SSM.lda 0
    SSM.ldc 3
    SSM.add 
    SSM.stl 1
    newBlock "__load_thunk_loop"
    SSM.ldl 1
    SSM.ldc 1
    SSM.ge 
    SSM.brf "__eval_thunk"
    SSM.ldl (-2)
    SSM.ldl 1
    SSM.sub 
    SSM.lda 1
    SSM.ldl 1
    SSM.ldc 1
    SSM.sub 
    SSM.stl 1
    SSM.bra "__load_thunk_loop"
    newBlock "__eval_thunk"
    SSM.ldl (-3)
    SSM.add 
    SSM.lds (-1)
    SSM.lds (-1)
    SSM.eq 
    SSM.brt "__eval_saturated_thunk"
    SSM.bsr "__store_thunk"
    removeStackFrame
    newBlock "__eval_saturated_thunk"
    SSM.stl 1
    SSM.stl 1
    SSM.jsr
    removeStackFrame

mkRuntimeSystem :: SSMMonad ()
mkRuntimeSystem = 
    let actions = [genEqInt,
                   genEqBool,
                   genEqChar,
                   genEqVoid,
                   genEqOrdList,
                   genEqOrdTup,
                   genOrdInt,
                   genOrdBool,
                   genOrdChar,
                   genOrdVoid,
                   genPrintInt,
                   genPrintBool,
                   genPrintChar,
                   genPrintVoid,
                   genPrintList,
                   genPrintTup,
                   genHd,
                   genTl,
                   genFst,
                   genSnd,
                   genPrint,
                   genCallThunkFun,
                   genStoreThunkFun] 
    in sequence_ actions
