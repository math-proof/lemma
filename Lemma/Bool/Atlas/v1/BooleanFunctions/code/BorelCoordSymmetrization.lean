import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.BooleanFunctions.code.BorelCoordSymmetrization
open MeasureTheory ProbabilityTheory Real Set GaussianStability


namespace GaussianStability

/--
[EuclideanSpace.updateCoord_same](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/BorelCoordSymmetrization.lean)
-/
@[path]
lemma EuclideanSpace.updateCoord_same
  {n : ℕ}
  {x : EuclideanSpace ℝ (Fin n)}
  {i : Fin n}
  {t : ℝ} :
-- imply
  (EuclideanSpace.updateCoord x i t) i = t := by
-- proof
  simp [EuclideanSpace.updateCoord, WithLp.equiv, Function.update_self]

end GaussianStability

namespace GaussianStability

/--
[EuclideanSpace.updateCoord_ne](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/BorelCoordSymmetrization.lean)
-/
@[path]
lemma EuclideanSpace.updateCoord_ne
  {n : ℕ}
  {x : EuclideanSpace ℝ (Fin n)}
  {i j : Fin n}
  {t : ℝ}
-- given
  (hij : j ≠ i) :
-- imply
  (EuclideanSpace.updateCoord x i t) j = x j := by
-- proof
  simp [EuclideanSpace.updateCoord, WithLp.equiv, Function.update_of_ne hij]

end GaussianStability

namespace GaussianStability

/--
[fiber_stability_le_symmetrized](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/BorelCoordSymmetrization.lean)
-/
@[path]
lemma fiber_stability_le_symmetrized
  {n : ℕ}
  {i : Fin n}
  {f : EuclideanSpace ℝ (Fin n) → ℝ}
  {ρ : ℝ}
  {x : EuclideanSpace ℝ (Fin n)}
-- given
  (hf_range : ∀ x, f x ∈ Icc (-1 : ℝ) 1)
  (hρ₀ : 0 ≤ ρ)
  (hρ₁ : ρ ≤ 1) :
-- imply
  fiberNoiseStability1D i f ρ x ≤ fiberNoiseStability1D_symmetrized i f ρ x := by
-- proof
  unfold fiberNoiseStability1D fiberNoiseStability1D_symmetrized
  have hg_range : ∀ t, f (EuclideanSpace.updateCoord x i t) ∈ Icc (-1 : ℝ) 1 :=
    fun t => hf_range _
  have hg_mean : ∫ t, f (EuclideanSpace.updateCoord x i t) ∂(gaussianReal 0 1) =
    conditionalMean i f x := rfl
  exact one_dim_noise_stability_le_threshold
    (fun t => f (EuclideanSpace.updateCoord x i t))
    hg_range
    (conditionalMean i f x)
    hg_mean
    ρ hρ₀ hρ₁
end GaussianStability



-- created on 2026-10-23
