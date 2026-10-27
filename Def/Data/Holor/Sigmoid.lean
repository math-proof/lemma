import Instance.Data.Holor.Tensor.Part2
import Instance.Data.Vector.Functions.Part2
open Tensor


/--
[sigmoid](https://pytorch.org/docs/stable/generated/torch.nn.functional.sigmoid.html)
-/
def Tensor.sigmoid [Exp α] (x : Tensor α s) : Tensor α s :=
  ⟨x.data.sigmoid⟩

