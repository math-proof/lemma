import Lemma.Tensor.DotDot.eq.Dot_Dot
import Lemma.Tensor.DotTShiftMatrix.eq.Eye
import Lemma.Tensor.EqDotEye
import Lemma.Tensor.EqTShiftMatrix
open Tensor


@[main]
private lemma main
  [Semiring α] [CharZero α]
-- given
  (x : Tensor α [n])
  (i j : Fin n) :
-- imply
  (ShiftMatrix (α := α) n i j)ᵀ @ ((ShiftMatrix (α := α) n i j) @ x) = x := by
-- proof
  have h : (ShiftMatrix (α := α) n j i) @ (ShiftMatrix (α := α) n i j) = Tensor.eye (α := α) n :=
    DotTShiftMatrix.eq.Eye n (i : ℕ) (j : ℕ) i.isLt j.isLt
  apply Eq.trans (DotDot.eq.Dot_Dot.mmv (ShiftMatrix (α := α) n i j)ᵀ (ShiftMatrix (α := α) n i j) x).symm
  rw [EqTShiftMatrix (α := α) n (i : ℕ) (j : ℕ)]
  show ((ShiftMatrix (α := α) n j i) @ (ShiftMatrix (α := α) n i j)) @ x = x
  rw [h]
  exact EqDotEye.mv x


-- created on 2020-11-13
