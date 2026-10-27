import Mathlib
import Initialize.Tactic.Attr.Basic
open MeasureTheory


/--
[markov_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/MarkovInequality.lean)
-/
@[path]
lemma markov_inequality
  {m : MeasurableSpace Ω}
  {μ : Measure Ω}
  {X : Ω → ℝ}
  {a : ℝ}
-- given
  (hX_nn : 0 ≤ᵐ[μ] X)
  (hX_int : Integrable X μ)
  (ha : 0 < a) :
-- imply
  μ.real {ω | a ≤ X ω} ≤ (∫ ω, X ω ∂μ) / a := by
-- proof
  rw [le_div_iff₀ ha, mul_comm]
  exact mul_meas_ge_le_integral_of_nonneg hX_nn hX_int a


-- created on 2026-10-23
