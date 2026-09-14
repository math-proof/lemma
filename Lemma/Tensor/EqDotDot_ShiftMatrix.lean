import Lemma.Tensor.DotDot.eq.Dot_Dot
import Lemma.Tensor.DotTShiftMatrix.eq.Eye
import Lemma.Tensor.EqDot_Eye
open Tensor


@[main]
private lemma main
  [Semiring α] [CharZero α]
-- given
  {n : ℕ}
  (x : Tensor α [n])
  (i j : Fin n) :
-- imply
  (x @ ShiftMatrix (α := α) i j) @ ShiftMatrix (α := α) j i = x := by
-- proof
  rw [DotDot.eq.Dot_Dot.vmm]
  rw [DotTShiftMatrix.eq.Eye j i]
  apply EqDot_Eye.vm


-- created on 2020-11-14
