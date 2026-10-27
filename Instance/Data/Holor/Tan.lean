import Def.Data.Holor.Defs.Part4
import Def.Analysis.SpecialFunctions.Trigonometric.Part2
import Def.Data.Holor.Tan
open Tensor


instance [Tan α] : Tan (Tensor α s) where
  tan := Tensor.tan

