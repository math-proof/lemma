import torch.Tensor
import sympy.vector.functions
open Tensor

/--
[sigmoid](https://pytorch.org/docs/stable/generated/torch.nn.functional.sigmoid.html)
-/
def Tensor.sigmoid [Exp α] (x : Tensor α s) : Tensor α s :=
  ⟨x.data.sigmoid⟩
