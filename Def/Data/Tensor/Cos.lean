module

public import Def.Data.Tensor.Defs.Part4
public import Def.Analysis.SpecialFunctions.Trigonometric.Part2

@[expose] public section

open Tensor


/--
[cos](https://pytorch.org/docs/stable/generated/torch.Tensor.cos.html)
Elementwise cosine. Available for `Tensor ℝ s` and `Tensor ℂ s` via `Cos`.
-/
def Tensor.cos [Cos α] (x : Tensor α s) : Tensor α s :=
  x.map Cos.cos

