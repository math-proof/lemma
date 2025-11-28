import sympy.tensor.Basic
import Lemma.Bool.SEq.is.EqCast.of.Eq
import Lemma.List.EqEraseIdx.of.LeLength
import Lemma.Tensor.SEqSum.of.LeLength
open Bool List Tensor


@[main, comm]
private lemma main
  [Add α] [Zero α]
  {d : ℕ}
-- given
  (h : s.length ≤ d)
  (X : Tensor α s) :
-- imply
  X.sum d = cast (congrArg (Tensor α) (Eq_EraseIdx.of.LeLength h)) X := by
-- proof
  apply Eq_Cast.of.SEq.Eq
  ·
    apply Eq_EraseIdx.of.LeLength h
  ·
    apply SEqSum.of.LeLength h


-- created on 2025-11-28
