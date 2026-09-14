import Lemma.Tensor.DotDot.eq.Dot_Dot
import torch.Tensor.permute
import Lemma.Tensor.DotTShiftMatrix.eq.Eye
import Lemma.Tensor.EqDotEye
import Lemma.Tensor.EqTShiftMatrix
open Tensor


@[main]
private lemma main
  [Semiring α] [CharZero α]
-- given
  {n : ℕ}
  (x : Tensor α [n])
  (i j : Fin n) :
-- imply
  (ShiftMatrix (α := α) i j)ᵀ @ ((ShiftMatrix (α := α) i j) @ x) = x := by
-- proof
  have h : (ShiftMatrix (α := α) j i) @ (ShiftMatrix (α := α) i j) =
      Tensor.eye (α := α) n :=
    DotTShiftMatrix.eq.Eye i j
  apply Eq.trans (DotDot.eq.Dot_Dot.mmv (ShiftMatrix (α := α) i j)ᵀ (ShiftMatrix (α := α) i j) x).symm
  rw [EqTShiftMatrix (α := α) i j]
  show ((ShiftMatrix (α := α) j i) @ (ShiftMatrix (α := α) i j)) @ x = x
  rw [h]
  exact EqDotEye.mv x


-- created on 2020-11-13
