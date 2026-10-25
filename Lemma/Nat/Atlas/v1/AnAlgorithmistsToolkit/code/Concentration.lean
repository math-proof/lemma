import Mathlib
import sympy.Basic
import Def.v1.Atlas.AnAlgorithmistsToolkit.code.HighDimensional.Part2
import Lemma.Nat.Atlas.v1.AnAlgorithmistsToolkit.code.HighDimensional
open MeasureTheory ProbabilityTheory Real InnerProductSpace
open MeasureTheory Real Set Finset BigOperators


namespace Concentration

/--
[inner_product_eq_dist_hyperplane](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/Concentration.lean)
-/
@[path]
lemma inner_product_eq_dist_hyperplane
  {n : ℕ}
  {a x : EuclideanSpace ℝ (Fin n)}
-- given
  (ha : ‖a‖ = 1) :
-- imply
  Metric.infDist x {y | @inner ℝ _ _ a y = (0 : ℝ)} = := by
-- proof
  set H := {y : EuclideanSpace ℝ (Fin n) | @inner ℝ _ _ a y = (0 : ℝ)}
  set c : ℝ := @inner ℝ _ _ a x
  set p := x - c • a
  have hp : p ∈ H := by
    simp only [H, Set.mem_setOf_eq, p, inner_sub_right, inner_smul_right,
      inner_self_eq_norm_sq_to_K, ha]
    simp [c]
  have hdist : dist x p = |c| := by
    simp only [p, dist_eq_norm, sub_sub_cancel]
    rw [norm_smul, ha, mul_one, Real.norm_eq_abs]
  have hne : H.Nonempty := ⟨p, hp⟩
  apply le_antisymm
  · rw [← hdist]
    exact Metric.infDist_le_dist_of_mem hp
  · rw [Metric.le_infDist hne]
    intro y hy
    rw [dist_eq_norm]
    have hinner : @inner ℝ _ _ a y = (0 : ℝ) := hy
    calc |c| = |@inner ℝ _ _ a (x - y)| := by
      simp only [c, inner_sub_right, hinner, sub_zero]
      _ ≤ ‖a‖ * ‖x - y‖ := abs_real_inner_le_norm a (x - y)
      _ = ‖x - y‖ := by rw [ha, one_mul]

end Concentration

namespace Concentration

/--
[levy_concentration_lipschitz](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/Concentration.lean)
-/
@[path]
lemma levy_concentration_lipschitz
  {n : ℕ}
  {f : UnitSphere n → ℝ}
  {M : ℝ}
  {ε : ℝ}
-- given
  (hf : LipschitzWith 1 f)
  (hM : IsMedian (uniformSphereMeasure n) f M)
  (hε : 0 < ε)
  (hne_low : {x : UnitSphere n | f x ≤ M}.Nonempty)
  (hne_high : {x : UnitSphere n | f x ≥ M}.Nonempty) :
-- imply
  uniformSphereMeasure n {x | ε < |f x - M|} ≤ ENNReal.ofReal (2 * exp (-(↑n * ε ^ 2 / 2))) :=
-- proof
  concentration_lipschitz_sphere n f hf M hM ε hε hne_low hne_high
end Concentration
namespace VolumeHardness
open MeasureTheory Real Set Finset BigOperators
end VolumeHardness



-- created on 2026-10-23
