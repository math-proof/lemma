import Def.Data.Tensor.Defs.Part4
import Def.Analysis.SpecialFunctions.Trigonometric.Part2
import Def.Data.Tensor.Sin
open Tensor


instance [Sin α] : Sin (Tensor α s) where
  sin := Tensor.sin

