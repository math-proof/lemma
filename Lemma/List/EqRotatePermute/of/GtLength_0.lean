import stdlib.List
import Lemma.List.Permute.eq.Rotate.of.GtLength_0
import Lemma.List.EqRotateRotate.of.Le_Length
open List


@[main, comm]
private lemma main
  {s : List ℕ}
-- given
  (h : s.length > 0) :
-- imply
  (s.permute ⟨0, h⟩ (s.length - 1 : ℕ)).rotate (s.length - 1) = s := by
-- proof
  rw [Permute.eq.Rotate.of.GtLength_0]
  rw [EqRotateRotate.of.Le_Length]
  omega


-- created on 2025-10-20
