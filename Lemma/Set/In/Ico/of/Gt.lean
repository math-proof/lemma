import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n b : ℤ}
-- given
  (h₀ : n > b) :
-- imply
  n ∈ Set.Ici (b + 1) := by
-- proof
  rw [Set.mem_Ici, Int.add_one_le_iff]
  omega


-- created on 2021-02-01
-- updated on 2026-10-26
