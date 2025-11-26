import Lemma.List.EqEraseIdx.of.LeLength
import Lemma.Tensor.CastDiv.eq.DivCast.of.Eq
import Lemma.Nat.NotLt.of.Ge
open List Tensor Nat


@[main]
private lemma main
  [DivisionSemiring α]
-- given
  (h : dim ≥ s.length)
  (X : Tensor α s)
  (n : Tensor α []) :
-- imply
  (X / n).sum dim = X.sum dim / n := by
-- proof
  unfold Tensor.sum
  simp [NotLt.of.Ge h]
  simp at h
  have h := EqEraseIdx.of.LeLength h
  rw [CastDiv.eq.DivCast.of.Eq.scalar h.symm X]


-- created on 2025-09-25
