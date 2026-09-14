import torch.Tensor.aminmax
open Tensor

/--
Returns the indices of the maximum value of a tensor along `dim`.
[argmax](https://docs.pytorch.org/docs/stable/generated/torch.Tensor.argmax.html)
-/
def Tensor.argmax [NeZero s.prod] [LT α] [DecidableLT α] (X : Tensor α s) (dim : Fin s.length) : Tensor (Fin s[dim]) (s.eraseIdx dim) :=
  X.argAminmax LT.lt dim
