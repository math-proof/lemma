import Def.Data.Holor.Defs.Part4
import Def.Analysis.SpecialFunctions.Trigonometric.Part2
import Def.Data.Holor.Cot
open Tensor


instance [Cot α] : Cot (Tensor α s) where
  cot := Tensor.cot

