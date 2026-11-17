module

public import Lean
public import Def.Lean.ConstructorVal

@[expose] public section

open Lean


instance : ToJson ConstructorVal where
  toJson := ConstructorVal.toJson

