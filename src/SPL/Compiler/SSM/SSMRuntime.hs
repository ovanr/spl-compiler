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

genEqList = do
    startLoop <- newLabel "loop_start" 
    success <- newLabel "success" 
    failure <- newLabel "failure" 
    newBlock "_eq_list"
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
    SSM.lda 0 
    SSM.ldl (-3)
    SSM.lda 0 
    SSM.ldl (-2)
    SSM.jsr
    SSM.ajs (-2)
    SSM.ldr RR
    SSM.brf failure
    SSM.ldl (-4)
    SSM.ldc 1
    SSM.sub
    SSM.stl (-4)
    SSM.ldl (-3)
    SSM.ldc 1
    SSM.sub
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

genEqTup = do 
    failure <- newLabel "failure"
    newBlock "_eq_tup"
    SSM.link 0
    SSM.ldl (-5)
    SSM.lda 0
    SSM.ldl (-4)
    SSM.lda 0
    SSM.ldl (-2)
    SSM.jsr
    SSM.ajs (-2)
    SSM.ldr RR
    SSM.brf failure
    SSM.ldl (-5)
    SSM.ldc 1
    SSM.sub
    SSM.lda 0
    SSM.ldl (-4)
    SSM.ldc 1
    SSM.sub
    SSM.lda 0
    SSM.ldl (-3)
    SSM.jsr
    SSM.ajs (-2)
    SSM.ldr RR
    SSM.brf failure
    ldc True
    SSM.str RR
    removeStackFrame
    newBlock failure
    ldc False
    SSM.str RR
    removeStackFrame

-- "_ord_int"
-- "_ord_bool"
-- "_ord_char"
-- "_ord_void"
-- "_ord_list"
-- "_ord_tup"
-- "_print_int"
-- "_print_bool"
-- "_print_char"
-- "_print_void"
-- "_print_list"
-- "_print_tup"

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
                   genEqList,
                   genEqTup,
                   genCallThunkFun,
                   genStoreThunkFun] 
    in sequence_ actions
