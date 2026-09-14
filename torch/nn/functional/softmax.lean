import torch.Tensor.exp
import torch.Tensor.sum
import torch.utils
open Tensor

/--
[softmax](https://pytorch.org/docs/stable/generated/torch.nn.functional.softmax.html)
-/
def Tensor.softmax [Exp α] (x : Tensor α s) (dim : ℕ := s.length - 1) : Tensor α s :=
  let x_exp := exp x
  x_exp / (x_exp.sum dim).keepdim
