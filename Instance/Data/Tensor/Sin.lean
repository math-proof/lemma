module

public import Def.Data.Tensor.Defs.Part4
public import Def.Analysis.SpecialFunctions.Trigonometric.Part2
public import Def.Data.Tensor.Sin
@[expose] public section

open Tensor


instance [Sin α] : Sin (Tensor α s) where
  sin := Tensor.sin

