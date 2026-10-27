import Lean
import Def.Lean.ConstructorVal.Part2
open Lean


instance : ToString ConstructorVal where
  toString := ConstructorVal.toString

