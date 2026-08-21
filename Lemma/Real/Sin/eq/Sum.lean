import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import sympy.functions.combinatorial.factorials
import sympy.functions.elementary.trigonometric
import sympy.series.limits
import sympy.sets.sets
import sympy.Basic
open Filter


@[main]
private lemma main
-- given
  (x : ℝ) :
-- imply
  sin x = lim [N → ∞] ∑ n ∈ range N, (-1) ^ n * x ^ (2 * n + 1) / ((2 * n + 1) !) := by
-- proof
  have h := (Real.hasSum_sin x).tendsto_sum_nat
  simpa using h.limUnder_eq.symm


-- created on 2018-06-02
-- updated on 2026-08-20
