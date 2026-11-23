module

public import Def.Data.Tensor.Defs.Part4
public import Def.Analysis.SpecialFunctions.Trigonometric.Part2
public import Def.Data.Tensor.Cot
@[expose] public section

open Tensor


instance [Cot α] : Cot (Tensor α s) where
  cot := Tensor.cot

