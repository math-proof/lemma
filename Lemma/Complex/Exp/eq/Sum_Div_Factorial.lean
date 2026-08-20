import Mathlib.Analysis.SpecialFunctions.Exponential
import sympy.functions.combinatorial.factorials
import sympy.functions.elementary.exponential
import sympy.series.limits
import sympy.sets.sets
open Filter


@[main]
private lemma maclaurin
-- given
  (x : ℂ) :
-- imply
  exp x = lim [N → ∞] ∑ n ∈ range N, x ^ n / (n !) := by
-- proof
  have h := (NormedSpace.expSeries_div_hasSum_exp x).tendsto_sum_nat
  simpa [Exp.exp, Complex.exp_eq_exp_ℂ] using h.limUnder_eq.symm


-- created on 2026-08-19
