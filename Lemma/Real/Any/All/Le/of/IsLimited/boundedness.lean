import sympy.concrete.quantifier
import sympy.series.limits
import sympy.sets.sets
import sympy.Basic
open Set


@[path]
private lemma main
  {f : ℝ → ℝ}
  {x₀ a : ℝ}
-- given
  (h : lim [x → x₀] f x = a) :
-- imply
  ∃ M > 0, ∃ δ > 0, ∀ x | |x - x₀| ∈ Ioo 0 δ, |f x| ≤ M := by
-- proof
  sorry


-- created on 2026-10-11
