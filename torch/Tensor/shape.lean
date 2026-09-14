import sympy.tensor.Basic
open Tensor

/--
The shape of the tensor (the list of its dimension sizes).
Mirrors the read-only attribute
[`torch.Tensor.shape`](https://docs.pytorch.org/docs/stable/tensors.html#tensor-attributes).
-/
def Tensor.shape (_ : Tensor α s) : List ℕ := s
