module
public import Instance.Data.Tensor.Tensor
public import Def.Data.Tensor.Aminmax
open Tensor


public section

/--
Reduces the tensor along `dim` by taking the minimum value.
[min](https://docs.pytorch.org/docs/stable/generated/torch.Tensor.min.html)
-/
def Tensor.min [NeZero s.prod] [LT α] [DecidableLT α] (X : Tensor α s) (dim : ℕ := s.length - 1) : Tensor α (s.eraseIdx dim) :=
  X.aminmax GT.gt dim

