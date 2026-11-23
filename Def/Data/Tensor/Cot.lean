module

public import Def.Data.Tensor.Defs.Part4
public import Def.Analysis.SpecialFunctions.Trigonometric.Part2

@[expose] public section

open Tensor


/--
[cot](https://pytorch.org/docs/stable/generated/torch.Tensor.cot.html)
Elementwise cotangent. Available for `Tensor ℝ s` and `Tensor ℂ s` via `Cot`.
-/
def Tensor.cot [Cot α] (x : Tensor α s) : Tensor α s :=
  x.map Cot.cot

