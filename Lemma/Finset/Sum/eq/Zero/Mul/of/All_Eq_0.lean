import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {f : ℕ → ℂ}
  {w : ℕ → ℂ}
-- given
  (h : ∀ i < n, f i = 0) :
-- imply
  ∑ i ∈ Finset.range n, f i * w i = 0 := by
-- proof
  exact Finset.sum_eq_zero (fun i hi => by rw [h i (Finset.mem_range.mp hi), zero_mul])


-- created on 2026-09-27
