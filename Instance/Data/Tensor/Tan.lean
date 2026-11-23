module

public import Def.Data.Tensor.Defs.Part4
public import Def.Analysis.SpecialFunctions.Trigonometric.Part2
public import Def.Data.Tensor.Tan
@[expose] public section

open Tensor


instance [Tan α] : Tan (Tensor α s) where
  tan := Tensor.tan

