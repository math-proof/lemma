import Lemma.List.Permute_SubLength_0.eq.AppendRotateTake___Drop.of.GtLength_0
open List


@[main, comm]
private lemma main
  {s : List ℕ}
-- given
  (h : s.length > 0) :
-- imply
  s.permute ⟨s.length - 1, by grind⟩ (-(s.length - 1 : ℕ)) = s.rotate (s.length - 1) := by
-- proof
  simp [Permute_SubLength_0.eq.AppendRotateTake___Drop.of.GtLength_0 h]


-- created on 2025-10-26
