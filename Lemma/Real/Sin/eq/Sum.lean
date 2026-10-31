import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Def.Data.Nat.Factorial.Factorials
import Def.Analysis.SpecialFunctions.Trigonometric.Part2
import Def.Analysis.Real.Limits.Basic
import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
-- given
  (x : ℝ) :
-- imply
  sin x = lim [N → ∞] ∑ n ∈ range N, (-1) ^ n * x ^ (2 * n + 1) / ((2 * n + 1) !) := by
-- proof
  have h := (Real.hasSum_sin x).tendsto_sum_nat
  simpa using h.limUnder_eq.symm


-- created on 2018-06-02
-- updated on 2026-10-26
