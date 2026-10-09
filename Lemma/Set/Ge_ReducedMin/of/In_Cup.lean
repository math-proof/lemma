import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {x : ℕ → ℝ}
  {c : ℝ}
-- given
  (h : c ∈ Finset.image x (Finset.range n)) :
-- imply
  Finset.min' (Finset.image x (Finset.range n)) ⟨c, h⟩ ≤ c := by
-- proof
  exact Finset.min'_le _ c h


-- created on 2023-11-12
