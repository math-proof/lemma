import sympy.core.function
import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {f : ℕ → ℝ → ℝ} :
-- imply
  Difference (fun x => ∑ i ∈ Finset.range n, f i x) 1 = fun x => ∑ i ∈ Finset.range n, Difference (f i) 1 x := by
-- proof
  funext x
  simp [Difference, fwdDiff, Finset.sum_sub_distrib]


-- created on 2020-10-11
