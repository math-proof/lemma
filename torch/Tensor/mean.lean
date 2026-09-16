import torch.Tensor.Basic
import torch.Tensor.sum
open Tensor

/--
[torch.mean](https://docs.pytorch.org/docs/stable/generated/torch.mean.html)

Compute the mean of a tensor along a given dimension.
use (X.mean dim).keepdim to keep the dimension
-/
def Tensor.mean [Add α] [Zero α] [Div α] [NatCast α] (X : Tensor α s) (dim : ℕ := s.length - 1) : Tensor α (s.eraseIdx dim) :=
  let size := if h_dim : dim < s.length then s.get ⟨dim, h_dim⟩ else 1
  X.sum dim / (size : α)
