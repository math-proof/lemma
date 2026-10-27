import Mathlib.Probability.Moments.Variance
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory


@[path]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω} [IsFiniteMeasure π]
  {x : ι → Ω → ℝ} [Fintype ι]
-- given
  (h₀ : ∀ i, MemLp (x i) 2 π) :
-- imply
  variance (fun ω => ∑ i, x i ω) π = ∑ i, ∑ j, covariance (x i) (x j) π :=
-- proof
  variance_fun_sum h₀


-- created on 2023-04-19
-- updated on 2026-10-26
