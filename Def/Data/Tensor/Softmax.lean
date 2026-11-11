import Instance.Data.Tensor.Exp
import Def.Data.Tensor.Sum
import Def.Data.Tensor.Utils
open Tensor


/--
[softmax](https://pytorch.org/docs/stable/generated/torch.nn.functional.softmax.html)
-/
def Tensor.softmax [Exp α] (x : Tensor α s) (dim : ℕ := s.length - 1) : Tensor α s :=
  let x_exp := Exp.exp x
  x_exp / (x_exp.sum dim).keepdim

