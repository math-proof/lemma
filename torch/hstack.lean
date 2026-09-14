import sympy.tensor.Basic
open Tensor

/--
[hstack](https://docs.pytorch.org/docs/stable/generated/torch.hstack.html)

Horizontal concatenation along the second axis. Rank ≥ 2 only (no 1D case).
-/
def Tensor.hstack (A : Tensor α (d :: n :: s)) (B : Tensor α (d :: m :: s)) :
    Tensor α (d :: (n + m) :: s) :=
  let A : Tensor α ([d] ++ n :: s) := A
  let B : Tensor α ([d] ++ m :: s) := B
  A ++ B
