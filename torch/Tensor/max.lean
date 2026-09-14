import sympy.tensor.tensor
import torch.Tensor.aminmax
open Tensor

/--
Reduces the tensor along `dim` by taking the maximum value.
[max](https://docs.pytorch.org/docs/stable/generated/torch.Tensor.max.html)
-/
def Tensor.max [NeZero s.prod] [LT α] [DecidableLT α] (X : Tensor α s) (dim : ℕ := s.length - 1) : Tensor α (s.eraseIdx dim) :=
  X.aminmax LT.lt dim
