import Lemma.List.EraseIdx_Succ.eq.Cons_EraseIdxTail.of.GtLength_0
import Lemma.Nat.EqAddSub.of.Ge
import Lemma.Nat.Succ.eq.Add_1
open List Nat


@[main]
private lemma main
-- given
  (h : i > 0)
  (s : List α) :
-- imply
  (s₀ :: s).eraseIdx i = s₀ :: s.eraseIdx (i - 1) := by
-- proof
  have h := EraseIdx_Succ.eq.Cons_EraseIdxTail.of.GtLength_0 (by simp) (i - 1) (s := s₀ :: s)
  rw [Succ.eq.Add_1] at h
  rw [EqAddSub.of.Ge (by omega)] at h
  simp [h]


-- created on 2025-10-09
