import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.ProjectionTheory.code.BourgainCorollary
open BourgainProjection
open MeasureTheory Real Set


namespace BourgainProjection

/--
[avg_projection_covering_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/BourgainCorollary.lean)
-/
@[path]
lemma avg_projection_covering_bound
  {f : ℝ → EuclideanSpace ℝ (Fin 2) → ℝ}
  {X : ℕ → Set (EuclideanSpace ℝ (Fin 2))}
  {δ : NNReal}
  {C₁ : ℝ}
  {C₂ : ℝ}
-- given
  (hδ : (0 : ℝ) < δ)
  (hC₁ : C₁ > 0)
  (hdecomp : ∀ j, coveringNum δ (X (j + 1)) ≥ C₁ * (δ : ℝ)⁻¹ * avgFamilyCovering f δ (X j) 0 1)
  (hC₂ : C₂ > 0)
  (havgest : ∀ j, avgFamilyCovering f δ (X j) 0 1 ≥ C₂ * (coveringNum δ (X j)) ^ (1/2 : ℝ)) :
-- imply
  ∃ C : ℝ, C > 0 ∧ ∀ j, coveringNum δ (X (j + 1)) ≥ C * (δ : ℝ)⁻¹ * (coveringNum δ (X j)) ^ (1/2 : ℝ) := by
-- proof
  refine ⟨C₁ * C₂, by positivity, fun j => ?_⟩
  calc coveringNum δ (X (j + 1))
    ≥ C₁ * (δ : ℝ)⁻¹ * avgFamilyCovering f δ (X j) 0 1 := hdecomp j
    _ ≥ C₁ * (δ : ℝ)⁻¹ * (C₂ * (coveringNum δ (X j)) ^ (1/2 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left (havgest j)
      apply mul_nonneg (le_of_lt hC₁) (le_of_lt (inv_pos.mpr hδ))
    _ = C₁ * C₂ * (δ : ℝ)⁻¹ * (coveringNum δ (X j)) ^ (1/2 : ℝ) := by ring

end BourgainProjection


-- created on 2026-10-23
