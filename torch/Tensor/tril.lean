import torch.Tensor.masked_fill
open Tensor

/--
[torch.tril](https://docs.pytorch.org/docs/stable/generated/torch.tril.html)
-/
def Tensor.tril [Zero α] (X : Tensor α s) (diagonal : ℤ) : Tensor α s := X.masked_fill diagonal (· > ·)
