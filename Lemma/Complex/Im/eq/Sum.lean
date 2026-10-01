import sympy.functions.elementary.complexes
import sympy.Basic
open Real


@[main]
private lemma main
  {n : ℕ}
  {x : ℝ}
  {f : ℕ → ℝ → ℂ} :
-- imply
  im (∑ k ∈ Finset.range n, f k x) = ∑ k ∈ Finset.range n, im (f k x) := by
-- proof
  exact Complex.im_sum _ _


-- created on 2026-09-27
