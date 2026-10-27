import Def.Data.Holor.Defs.Part4
open Tensor


/--
[torch.Tensor.item](https://docs.pytorch.org/docs/stable/generated/torch.Tensor.item.html)
-/
def Tensor.item (X : Tensor α []) : α :=
  X.data[0]

