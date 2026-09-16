import torch.Tensor.Basic
import sympy.functions.elementary.trigonometric
open Tensor

/--
[cos](https://pytorch.org/docs/stable/generated/torch.Tensor.cos.html)
Elementwise cosine. Available for `Tensor ℝ s` and `Tensor ℂ s` via `Cos`.
-/
def Tensor.cos [Cos α] (x : Tensor α s) : Tensor α s :=
  x.map Cos.cos

instance [Cos α] : Cos (Tensor α s) where
  cos := Tensor.cos
