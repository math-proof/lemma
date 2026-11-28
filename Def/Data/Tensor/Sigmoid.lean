module

public import Instance.Data.Tensor.Tensor
public import Instance.Data.Vector.Functions

@[expose] public section

open Tensor


/--
[sigmoid](https://pytorch.org/docs/stable/generated/torch.nn.functional.sigmoid.html)
-/
def Tensor.sigmoid [Exp α] (x : Tensor α s) : Tensor α s :=
  ⟨x.data.sigmoid⟩

