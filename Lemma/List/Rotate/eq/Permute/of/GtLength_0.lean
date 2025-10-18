import stdlib.List
import Lemma.List.Permute.eq.AppendRotateTake___Drop.of.EqVal_0
import Lemma.Nat.EqAddSub.of.Ge
open List Nat


@[main, comm]
private lemma main
  {s : List ℕ}
-- given
  (h : s.length > 0) :
-- imply
  s.rotate 1 = s.permute ⟨0, h⟩ (s.length - 1 : ℕ) := by
-- proof
  simp [Permute.eq.AppendRotateTake___Drop.of.EqVal_0]
  rw [EqAddSub.of.Ge (by omega)]
  simp


-- created on 2025-10-18
