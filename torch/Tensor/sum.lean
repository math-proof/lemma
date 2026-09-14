import sympy.tensor.Basic
open Tensor

/--
[torch.sum](https://docs.pytorch.org/docs/stable/generated/torch.sum.html)
use (X.sum dim).keepdim to keep the dimension
-/
def Tensor.sum [Add α] [Zero α] (X : Tensor α s) (dim : ℕ := s.length - 1) : Tensor α (s.eraseIdx dim) :=
  ⟨cast (by simp; grind) ((X.data.splitAt dim).map fun x => (x.splitAt 1).sum).flatten⟩
