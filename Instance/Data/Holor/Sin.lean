import Def.Data.Holor.Defs.Part4
import Def.Analysis.SpecialFunctions.Trigonometric.Part2
import Def.Data.Holor.Sin
open Tensor


instance [Sin α] : Sin (Tensor α s) where
  sin := Tensor.sin

