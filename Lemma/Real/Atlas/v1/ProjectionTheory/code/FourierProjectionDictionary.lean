import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.ProjectionTheory.code.FourierProjectionDictionary
open MeasureTheory VectorFourier FourierProjection


namespace FourierProjection

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/--
[innerₗ_add_orthogonal_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/FourierProjectionDictionary.lean)
-/
@[path]
product: `⟨y + z, ξ⟩_E = ⟨y, ξ⟩_V`. This identifies the phase appearing in the
Fourier integral on `E` with the phase on `V`. -/
lemma innerₗ_add_orthogonal_eq (V : Submodule ℝ E)
  (y ξ : ↥V) (z : ↥(Vᗮ)) :
  (innerₗ E) ((↑y : E) + (↑z : E)) (↑ξ : E) = (innerₗ ↥V) y ξ := by
  simp only [innerₗ_apply_apply, inner_add_left]
  rw [V.coe_inner]
  have hz : @inner ℝ E _ (z : E) (ξ : E) = 0 :=
    Submodule.inner_left_of_mem_orthogonal ξ.2 z.2
  linarith

end FourierProjection

namespace FourierProjection

/--
[fourier_projection_dictionary](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/FourierProjectionDictionary.lean)
-/
@[path]
lemma fourier_projection_dictionary
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  [MeasurableSpace E]
  {V : Submodule ℝ E}
  {μ_V : Measure ↥V}
  {μ_perp : Measure ↥(Vᗮ)}
  {μ_E : Measure E}
  {f : E → ℂ}
  {ξ : ↥V}
-- given
  (hμ : ∀ g : E → ℂ, Integrable g μ_E → ∫ x : E, g x ∂μ_E = ∫ y : ↥V, ∫ z : ↥(Vᗮ), g ((y : E) + (z : E)) ∂μ_perp ∂μ_V)
  (hfξ_int : Integrable (fun x => Real.fourierChar (-(innerₗ E x (ξ : E))) • f x) μ_E) :
-- imply
  fourierIntegral Real.fourierChar μ_V (innerₗ ↥V) (subspaceProjection V μ_perp f) ξ = fourierIntegral Real.fourierChar μ_E (innerₗ E) f (↑ξ : E) := by
-- proof
  simp only [fourierIntegral]
  rw [hμ _ hfξ_int]
  congr 1
  ext y
  simp_rw [innerₗ_add_orthogonal_eq V y ξ]
  simp only [subspaceProjection]
  simp_rw [Circle.smul_def]
  exact (integral_smul _ _).symm

end FourierProjection

/--
[inner](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/FourierProjectionDictionary.lean)
-/
@[path]
private lemma inner_eq
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {V : Submodule ℝ E}
  {y ξ : ↥V}
  {z : ↥(Vᗮ)} :
-- imply
  (innerₗ E) ((↑y : E) + (↑z : E)) (↑ξ : E) = (innerₗ ↥V) y ξ := by
-- proof
  apply FourierProjection.inner V y ξ z


-- created on 2026-10-23
