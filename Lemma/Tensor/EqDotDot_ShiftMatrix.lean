import Lemma.Tensor.DotDot.eq.Dot_Dot
import Lemma.Tensor.DotTShiftMatrix.eq.Eye
import Lemma.Tensor.EqDot_Eye
open Tensor


@[main]
private lemma main
  [Semiring α] [CharZero α]
-- given
  (x : Tensor α [n])
  (i j : Fin n) :
-- imply
  (x @ ShiftMatrix (α := α) n i j) @ ShiftMatrix (α := α) n j i = x := by
-- proof
  rw [DotDot.eq.Dot_Dot.vmm]
  rw [DotTShiftMatrix.eq.Eye n j i j.isLt i.isLt]
  apply EqDot_Eye.vm


-- created on 2020-11-14
