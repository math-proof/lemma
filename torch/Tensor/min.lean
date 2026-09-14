import sympy.tensor.tensor
import torch.Tensor.aminmax
open Tensor

/--
Reduces the tensor along `dim` by taking the minimum value.
[min](https://docs.pytorch.org/docs/stable/generated/torch.Tensor.min.html)
-/
def Tensor.min [NeZero s.prod] [LT α] [DecidableLT α] (X : Tensor α s) (dim : ℕ := s.length - 1) : Tensor α (s.eraseIdx dim) :=
  X.aminmax GT.gt dim
