{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ExtendedDefaultRules #-}

module SPL.Compiler.SSM.SSMRuntime where

import Data.Text (Text)
import SPL.Compiler.SSM.SSMGenLib
import qualified SPL.Compiler.SSM.SSMGenLib as SSM

default (Int, Text) 

genStoreThunkFun :: SSMMonad ()
genStoreThunkFun = do
    newBlock "store_thunk"
    SSM.link 1
    SSM.ldl (-2)
    SSM.ldc 4
    SSM.add
    SSM.stl 1
    newBlock "store_thunk_loop"
    SSM.ldl 1
    SSM.ldc 1
    SSM.eq
    SSM.brt "end_store_thunk"
    SSM.ldr MP
    SSM.ldl 1
    SSM.sub
    SSM.lda 0
    SSM.sth
    SSM.ldl 1
    SSM.ldc 1
    SSM.sub
    SSM.stl 1
    SSM.bra "store_thunk_loop"
    newBlock "end_store_thunk"
    SSM.str RR
    removeStackFrame

genCallThunkFun :: SSMMonad ()
genCallThunkFun = do
    newBlock "call_thunk"
    SSM.link 1
    SSM.ldl (-3)
    SSM.stl 1
    newBlock "load_args_loop"
    SSM.ldl 1
    SSM.ldc 1
    SSM.ge
    SSM.brf "load_thunk"
    SSM.ldr MP 
    SSM.ldl 1
    SSM.sub 
    SSM.lda (-3)
    SSM.ldl 1
    SSM.ldc 1
    SSM.sub 
    SSM.stl 1
    SSM.bra "load_args_loop"
    newBlock "load_thunk"
    SSM.ldl (-2)
    SSM.lda 0
    SSM.ldc 3
    SSM.add 
    SSM.stl 1
    newBlock "load_thunk_loop"
    SSM.ldl 1
    SSM.ldc 1
    SSM.ge 
    SSM.brf "eval_thunk"
    SSM.ldl (-2)
    SSM.ldl 1
    SSM.sub 
    SSM.lda 1
    SSM.ldl 1
    SSM.ldc 1
    SSM.sub 
    SSM.stl 1
    SSM.bra "load_thunk_loop"
    newBlock "eval_thunk"
    SSM.ldl (-3)
    SSM.add 
    SSM.lds (-1)
    SSM.lds (-1)
    SSM.eq 
    SSM.brt "eval_saturated_thunk"
    SSM.bsr "store_thunk"
    removeStackFrame
    newBlock "eval_saturated_thunk"
    SSM.stl 1
    SSM.stl 1
    SSM.jsr
    removeStackFrame
