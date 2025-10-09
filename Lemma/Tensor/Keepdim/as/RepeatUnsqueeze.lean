import stdlib.SEq
import sympy.tensor.functions
import Lemma.Bool.SEq.of.EqCast.Eq
import Lemma.List.Lt_LengthInsertIdxEraseIdx.of.Lt_Length
import Lemma.List.EqSetInsertIdxEraseIdx.of.Lt_Length
open List Bool


@[main]
private lemma main
  {dim : ℕ}
  {s : List ℕ}
-- given
  (X : Tensor α (s.eraseIdx dim))
  (h : dim < s.length) :
-- imply
  X.keepdim ≃ (X.unsqueeze dim).repeat s[dim] ⟨dim, Lt_LengthInsertIdxEraseIdx.of.Lt_Length h 1⟩ := by
-- proof
  apply SEq.of.EqCast.Eq
  ·
    unfold Tensor.keepdim
    simp [h]
  ·
    simp [EqSetInsertIdxEraseIdx.of.Lt_Length h]


-- created on 2025-10-03
-- updated on 2025-10-04
