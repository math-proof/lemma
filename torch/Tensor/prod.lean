import torch.Tensor.Basic
open Tensor

/--
[torch.prod](https://docs.pytorch.org/docs/stable/generated/torch.prod.html)
use (X.prod dim).keepdim to keep the dimension
-/
def Tensor.prod [Mul α] [One α] (X : Tensor α s) (dim : ℕ := s.length - 1) : Tensor α (s.eraseIdx dim) :=
  ⟨cast (by simp; grind) ((X.data.splitAt dim).map fun x => (x.splitAt 1).prod).flatten⟩
