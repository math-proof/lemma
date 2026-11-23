module

public import Def.Data.Tensor.Defs.Part4
public import Def.Analysis.SpecialFunctions.Trigonometric.Part2
public import Def.Data.Tensor.Cos
@[expose] public section

open Tensor


instance [Cos α] : Cos (Tensor α s) where
  cos := Tensor.cos

