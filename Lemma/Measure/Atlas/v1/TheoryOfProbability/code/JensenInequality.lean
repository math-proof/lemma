import Mathlib
import Initialize.Tactic.Attr.Basic
open MeasureTheory MeasureTheory.Measure


/--
[jensen_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/JensenInequality.lean)
-/
@[path]
lemma jensen_inequality
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {X : Ω → ℝ}
  {φ : ℝ → ℝ}
-- given
  (hX_int : Integrable X μ)
  (hφ_convex : ConvexOn ℝ Set.univ φ)
  (hφX_int : Integrable (φ ∘ X) μ) :
-- imply
  φ (∫ ω, X ω ∂μ) ≤ ∫ ω, φ (X ω) ∂μ :=
-- proof
  hφ_convex.map_integral_le (hφ_convex.continuousOn isOpen_univ) isClosed_univ
    (Filter.Eventually.of_forall fun _ => Set.mem_univ _) hX_int hφX_int


-- created on 2026-10-23
