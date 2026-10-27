import Def.Data.Holor.Defs.Part4
import Def.Analysis.SpecialFunctions.Trigonometric.Part2
import Def.Data.Holor.Cos
open Tensor


instance [Cos α] : Cos (Tensor α s) where
  cos := Tensor.cos

