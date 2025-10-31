import Lemma.List.Permute.eq.AppendRotateTake___Drop.of.EqVal_0
open List


@[main]
private lemma main
  {s : List α}
-- given
  (h : s.length > 0)
  
  (d : ℕ) :
-- imply
  s.permute ⟨0, h⟩ d = (s.take (d + 1)).rotate 1 ++ s.drop (d + 1) := by
-- proof
  apply Permute.eq.AppendRotateTake___Drop.of.EqVal_0
  simp


-- created on 2025-10-31
