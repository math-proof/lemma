import torch.Tensor.aminmax
open Tensor

/--
Returns the indices of the minimum value of a tensor along `dim`.
[argmin](https://docs.pytorch.org/docs/stable/generated/torch.Tensor.argmin.html)
-/
def Tensor.argmin [NeZero s.prod] [LT α] [DecidableLT α] (X : Tensor α s) (dim : Fin s.length) : Tensor (Fin s[dim]) (s.eraseIdx dim) :=
  X.argAminmax GT.gt dim
