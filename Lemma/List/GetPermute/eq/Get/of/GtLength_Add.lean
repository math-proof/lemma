import Lemma.List.Permute.eq.Ite
import Initialize.Tactic.Attr.Basic
import Theorem.Data.List.List.Part2
open List


@[path]
private lemma main
  {s : List α}
-- given
  (h : s.length > i + d) :
-- imply
  have : i + d < (s.permute ⟨i, by grind⟩ d).length := by
    rw [List.length_permute]
    omega
  (s.permute ⟨i, by omega⟩ d)[i + d] = s[i] := by
-- proof
  simp [Permute.eq.Ite]
  split_ifs <;>
  .
    unfold List.slice List.array_slice
    simp
    grind


-- created on 2025-10-28
