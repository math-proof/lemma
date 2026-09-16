import torch.Tensor.Basic
import sympy.functions.elementary.trigonometric
open Tensor

/--
[sin](https://pytorch.org/docs/stable/generated/torch.Tensor.sin.html)
Elementwise sine. Available for `Tensor ℝ s` and `Tensor ℂ s` via `Sin`.
-/
def Tensor.sin [Sin α] (x : Tensor α s) : Tensor α s :=
  x.map Sin.sin

instance [Sin α] : Sin (Tensor α s) where
  sin := Tensor.sin
