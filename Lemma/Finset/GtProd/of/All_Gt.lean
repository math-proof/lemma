import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {f g : ℕ → ℝ}
-- given
  (h₀ : n > 0)
  (hg : ∀ i, g i > 0)
  (h : ∀ i < n, f i > g i) :
-- imply
  ∏ i ∈ Finset.range n, f i > ∏ i ∈ Finset.range n, g i := by
-- proof
  exact Finset.prod_lt_prod_of_nonempty₀ (fun i _ => hg i) (fun i hi => h i (Finset.mem_range.mp hi)) (Finset.nonempty_range_iff.mpr (by omega))


-- created on 2019-01-20
