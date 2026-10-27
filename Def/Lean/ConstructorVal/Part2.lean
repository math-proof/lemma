import Lean
import Instance.Lean.ConstructorVal
open Lean


def Lean.ConstructorVal.toString (ctor : ConstructorVal) : String :=
  ToString.toString (toJson ctor)


