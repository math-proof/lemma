import Lemma.List.Permute.eq.Ite
open List


@[main, comm]
private lemma main
  {s : List α}
-- given
  (h : s.length > i + d) :
-- imply
  have : i < (s.permute ⟨i + d, by grind⟩ (-d)).length := by
    simp
    omega
  (s.permute ⟨i + d, h⟩ (-d))[i] = s[i + d] := by
-- proof
  simp [Permute.eq.Ite]
  split_ifs <;>
  .
    unfold List.slice List.array_slice
    simp
    grind


-- created on 2025-10-28
