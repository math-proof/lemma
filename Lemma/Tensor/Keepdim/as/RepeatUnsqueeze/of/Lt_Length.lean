import stdlib.SEq
import sympy.tensor.functions
import Lemma.List.Lt_LengthInsertIdxEraseIdx.of.Lt_Length
import Lemma.Bool.SEq.is.EqCast.of.Eq
import Lemma.Tensor.Keepdim.eq.Cast_RepeatUnsqueeze.of.Lt_Length
open List Bool Tensor


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h : dim < s.length)
  (X : Tensor α (s.eraseIdx dim)) :
-- imply
  X.keepdim ≃ (X.unsqueeze dim).repeat s[dim] ⟨dim, Lt_LengthInsertIdxEraseIdx.of.Lt_Length h 1⟩ := by
-- proof
  apply SEq.of.Eq_Cast
  .
    apply Keepdim.eq.Cast_RepeatUnsqueeze.of.Lt_Length h X
  .
    simp
    apply List.EqSetInsertIdxEraseIdx.of.Lt_Length


-- created on 2025-10-09
