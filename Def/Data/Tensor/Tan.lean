module

public import Def.Data.Tensor.Defs.Part4
public import Def.Analysis.SpecialFunctions.Trigonometric.Part2

@[expose] public section

open Tensor


/--
[tan](https://pytorch.org/docs/stable/generated/torch.Tensor.tan.html)
Elementwise tangent. Available for `Tensor ℝ s` and `Tensor ℂ s` via `Tan`.
-/
def Tensor.tan [Tan α] (x : Tensor α s) : Tensor α s :=
  x.map Tan.tan

