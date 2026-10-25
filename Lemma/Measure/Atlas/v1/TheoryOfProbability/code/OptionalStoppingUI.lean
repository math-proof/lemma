import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.TheoryOfProbability.code.OptionalStoppingUI
open MeasureTheory Filter
open scoped ENNReal NNReal Topology


/--
[optional_stopping_uniformly_integrable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/OptionalStoppingUI.lean)
-/
@[path]
lemma optional_stopping_uniformly_integrable
  {m0 : MeasurableSpace Ω}
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m0}
  {M : ℕ → Ω → ℝ}
  {τ : Ω → ℕ}
-- given
  (hmart : Submartingale M ℱ μ)
  (hui : UniformIntegrable M 1 μ)
  (hτ : IsStoppingTime ℱ (fun ω => (τ ω : ℕ∞))) :
-- imply
  UniformIntegrable (fun n ω => M (min (τ ω) n) ω) 1 μ :=
-- proof
  optional_stopping_alt_ui_preserved hmart hui hτ


-- created on 2026-10-23
