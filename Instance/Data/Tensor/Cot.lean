import Def.Data.Tensor.Defs.Part4
import Def.Analysis.SpecialFunctions.Trigonometric.Part2
import Def.Data.Tensor.Cot
open Tensor


instance [Cot α] : Cot (Tensor α s) where
  cot := Tensor.cot

