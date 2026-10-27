import Def.Data.Holor.Defs.Part4
import Def.Analysis.SpecialFunctions.Trigonometric.Part2
open Tensor


/--
[cos](https://pytorch.org/docs/stable/generated/torch.Tensor.cos.html)
Elementwise cosine. Available for `Tensor ℝ s` and `Tensor ℂ s` via `Cos`.
-/
def Tensor.cos [Cos α] (x : Tensor α s) : Tensor α s :=
  x.map Cos.cos

