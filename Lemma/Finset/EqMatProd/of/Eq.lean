import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {f g : ℕ → ℂ}
-- given
  (h : ∀ i < n, f i = g i) :
-- imply
  ∏ i ∈ Finset.range n, f i = ∏ i ∈ Finset.range n, g i := by
-- proof
  exact Finset.prod_congr rfl (fun i hi => h i (Finset.mem_range.mp hi))


-- created on 2020-10-29
