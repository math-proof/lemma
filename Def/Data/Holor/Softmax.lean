import Instance.Data.Holor.Exp
import Def.Data.Holor.Sum
import Def.Data.Holor.Utils
open Tensor


/--
[softmax](https://pytorch.org/docs/stable/generated/torch.nn.functional.softmax.html)
-/
def Tensor.softmax [Exp α] (x : Tensor α s) (dim : ℕ := s.length - 1) : Tensor α s :=
  let x_exp := Exp.exp x
  x_exp / (x_exp.sum dim).keepdim

