import Lemma.List.EqEraseIdx.of.LeLength
import Lemma.Tensor.CastDiv.eq.DivCast.of.Eq
import Lemma.Nat.NotLt.of.Ge
open List Tensor Nat


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
  unfold Tensor.sum
  simp [NotLt.of.Ge h]
  have h := EqEraseIdx.of.LeLength h
  rw [CastDiv.eq.DivCast.of.Eq.scalar h.symm X]


-- created on 2025-09-25
