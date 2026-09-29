import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b : ℕ}
  {x : ℤ}
  {A : ℕ → Set ℤ}
-- given
  (h : ∀ k ∈ Finset.Ico a b, x ∉ A k) :
-- imply
  x ∉ ⋃ k ∈ Finset.Ico a b, A k := by
-- proof
  simp only [Set.mem_iUnion, not_exists]
  exact h


-- created on 2026-09-27
