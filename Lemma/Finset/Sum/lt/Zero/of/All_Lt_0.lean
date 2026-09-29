import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {f : ℕ → ℝ}
-- given
  (h₀ : n > 0)
  (h : ∀ i < n, f i < 0) :
-- imply
  ∑ i ∈ Finset.range n, f i < 0 := by
-- proof
  have := Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr (by omega))
    (fun i hi => h i (Finset.mem_range.mp hi) : ∀ i ∈ Finset.range n, f i < (fun _ => (0 : ℝ)) i)
  simpa using this


-- created on 2026-09-27
