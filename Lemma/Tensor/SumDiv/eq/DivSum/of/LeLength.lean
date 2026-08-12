import Lemma.List.EqEraseIdx.of.LeLength
import Lemma.Nat.NotLt.of.Ge
import Lemma.Tensor.CastDiv.eq.DivCast.of.Eq
import Lemma.Tensor.SEqSum.of.LeLength
open List Nat Tensor


@[main]
private lemma main
  [DivisionSemiring α]
-- given
  (h : s.length ≤ d)
  (X : Tensor α s)
  (n : Tensor α []) :
-- imply
  (X / n).sum d = X.sum d / n := by
-- proof
  rw [Sum.eq.Cast.of.LeLength (by grind)]
  conv_rhs => rw [Sum.eq.Cast.of.LeLength (by grind)]
  rw [CastDiv.eq.DivCast.of.Eq]
  apply Eq_EraseIdx.of.LeLength h


-- created on 2025-09-25
-- updated on 2026-07-22
