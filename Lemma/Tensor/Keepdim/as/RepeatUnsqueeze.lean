import Lemma.List.Lt_LengthInsertIdxEraseIdx.of.GtLength
import Lemma.Bool.SEq.is.EqCast.of.Eq
import Lemma.Tensor.Keepdim.eq.Cast_RepeatUnsqueeze
open List Bool Tensor


@[main]
private lemma main
  {s : List ℕ}
  {d : Fin s.length}
-- given
  (X : Tensor α (s.eraseIdx d)) :
-- imply
  X.keepdim ≃ (X.unsqueeze d).repeat s[d] ⟨d, Lt_LengthInsertIdxEraseIdx.of.GtLength d.isLt 1⟩ := by
-- proof
  apply SEq.of.Eq_Cast
  .
    apply Keepdim.eq.Cast_RepeatUnsqueeze
  .
    simp
    apply List.EqSetInsertIdxEraseIdx.of.GtLength


-- created on 2025-10-09
