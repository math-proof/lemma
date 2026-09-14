import torch.Tensor.masked_fill
open Tensor

/--
[torch.triu](https://docs.pytorch.org/docs/stable/generated/torch.triu.html)
-/
def Tensor.triu [Zero α] (X : Tensor α s) (diagonal : ℤ) : Tensor α s := X.masked_fill diagonal (· < ·)
