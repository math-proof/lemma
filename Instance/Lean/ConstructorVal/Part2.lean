module

public import Lean
public import Def.Lean.ConstructorVal.Part2
@[expose] public section

open Lean


instance : ToString ConstructorVal where
  toString := ConstructorVal.toString

