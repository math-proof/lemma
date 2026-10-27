import Lean
import Def.Lean.ConstructorVal
open Lean


instance : ToJson ConstructorVal where
  toJson := ConstructorVal.toJson

