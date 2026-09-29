import sympy.functions.elementary.complexes
import sympy.Basic
open Real


@[main]
private lemma main
  {n : ℕ}
  {x : ℝ}
  {f : ℕ → ℝ → ℂ} :
-- imply
  re (∑ k ∈ Finset.range n, f k x) = ∑ k ∈ Finset.range n, re (f k x) := by
-- proof
  exact Complex.re_sum _ _


-- created on 2026-09-27
