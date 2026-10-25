import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.DifferentialAnalysis.code.BorelMeasure
open MeasureTheory Measure Set TopologicalSpace MeasuresAndSigmaAlgebras
open scoped CompactlySupported ZeroAtInfty
open RealRMK


namespace MeasuresAndSigmaAlgebras

/--
[rieszMeasure_isBorelMeasure](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/BorelMeasure.lean)
-/
@[path]
lemma rieszMeasure_isBorelMeasure
  [TopologicalSpace X]
  [T2Space X]
  [MeasurableSpace X]
  {Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ} :
-- imply
  borel X ≤ (rieszMeasure Λ).toOuterMeasure.caratheodory := by
-- proof
  have h := le_toOuterMeasure_caratheodory (rieszMeasure Λ)
  rwa [← BorelSpace.measurable_eq]

end MeasuresAndSigmaAlgebras

namespace MeasuresAndSigmaAlgebras

/--
[rieszMeasureC0_isBorelMeasure](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/BorelMeasure.lean)
-/
@[path]
lemma rieszMeasureC0_isBorelMeasure
  [TopologicalSpace X]
  [T2Space X]
  [MeasurableSpace X]
  {Λ : C₀(X, ℝ) →ₗ[ℝ] ℝ}
-- given
  (hΛ : ∀ f : C₀(X, ℝ), (∀ x, 0 ≤ f x) → 0 ≤ Λ f) :
-- imply
  borel X ≤ (rieszMeasureOfC0Functional Λ hΛ).toOuterMeasure.caratheodory :=
-- proof
  rieszMeasure_isBorelMeasure (restrictC0ToCc Λ hΛ)

end MeasuresAndSigmaAlgebras


-- created on 2026-10-23
