module

public import Lean
public import Instance.Lean.ConstructorVal

@[expose] public section

open Lean


def Lean.ConstructorVal.toString (ctor : ConstructorVal) : String :=
  ToString.toString (toJson ctor)


