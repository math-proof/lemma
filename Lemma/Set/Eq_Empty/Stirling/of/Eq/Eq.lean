import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {k : ℕ}
  {x : Fin k → Set α}
  {j : Fin k}
-- given
  (h₀ : ∀ i, i ≠ j → Disjoint (x i) (x j)) :
-- imply
  (⋃ i ∈ ({i | i ≠ j} : Set (Fin k)), x i) ∩ x j = ∅ := by
-- proof
  ext a
  simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_empty_iff_false, iff_false]
  grind


-- created on 2021-03-27
-- updated on 2026-10-17
