import Lemma.List.Permute.eq.AppendRotateTake___Drop.of.EqVal_0
import Lemma.List.EqTakeAppend.of.Eq_Length
open List


@[main]
private lemma main
  {s : List α}
-- given
  (h : s.length > d) :
-- imply
  (s.permute ⟨0, by grind⟩ d).take (d + 1) = (s.take (d + 1)).rotate 1 := by
-- proof
  rw [Permute.eq.AppendRotateTake___Drop.of.EqVal_0 (by simp)]
  rw [EqTakeAppend.of.Eq_Length]
  simp
  omega


-- created on 2025-10-22
