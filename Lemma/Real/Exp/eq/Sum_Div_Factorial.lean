import Mathlib.Analysis.SpecialFunctions.Exponential
import Def.Data.Nat.Factorial.Factorials
import Initialize.Tactic.Attr.Basic
import Instance.Analysis.SpecialFunctions.Exponential
import Def.Analysis.Real.Limits.Basic
import Theorem.Data.Set.Sets
open Exp


@[path]
private lemma maclaurin
-- given
  (x : ℝ) :
-- imply
  exp x = lim[N → ∞] ∑ n ∈ range N, x ^ n / (n !) := by
-- proof
  have h := (NormedSpace.expSeries_div_hasSum_exp x).tendsto_sum_nat
  simpa [Exp.exp, Real.exp_eq_exp_ℝ] using h.limUnder_eq.symm


-- created on 2018-02-13
