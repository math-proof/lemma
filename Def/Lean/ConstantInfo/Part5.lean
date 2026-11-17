module

public import Lean

@[expose] public section

open Lean

def Lean.ConstantInfo.proof (info : ConstantInfo) : Expr :=
  info.value! (allowOpaque := true)
