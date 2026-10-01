import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {f g : ℕ → ℝ}
-- given
  (hf : ∀ i, f i ≥ 0)
  (h : ∀ i < n, f i ≤ g i) :
-- imply
  ∏ i ∈ Finset.range n, f i ≤ ∏ i ∈ Finset.range n, g i := by
-- proof
  exact Finset.prod_le_prod (fun i _ => hf i) (fun i hi => h i (Finset.mem_range.mp hi))


-- created on 2019-11-01
