import sympy.tensor.Basic
import sympy.functions.elementary.trigonometric
open Tensor

/--
[cot](https://pytorch.org/docs/stable/generated/torch.Tensor.cot.html)
Elementwise cotangent. Available for `Tensor ℝ s` and `Tensor ℂ s` via `Cot`.
-/
def Tensor.cot [Cot α] (x : Tensor α s) : Tensor α s :=
  x.map Cot.cot

instance [Cot α] : Cot (Tensor α s) where
  cot := Tensor.cot
