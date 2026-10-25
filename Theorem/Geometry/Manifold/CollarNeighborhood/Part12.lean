/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Def.Geometry.Manifold.CollarNeighborhood.Part11
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

theorem collarScaleIco_isOpenEmbedding (d : ℝ) (hd₀ : 0 < d) (hd₁ : d ≤ 1) :
    Topology.IsOpenEmbedding (collarScaleIco d hd₀ hd₁) := by
  let e : Set.Ico (0 : ℝ) 1 ≃ₜ Set.Ico (0 : ℝ) d :=
    { toFun := fun x ↦ ⟨d * x.val, mul_nonneg hd₀.le x.property.1,
          by simpa using mul_lt_mul_of_pos_left x.property.2 hd₀⟩
      invFun := fun y ↦ ⟨y.val / d, div_nonneg y.property.1 hd₀.le,
          (div_lt_one hd₀).2 y.property.2⟩
      left_inv := fun x ↦ by
        apply Subtype.ext
        exact mul_div_cancel_left₀ x.val hd₀.ne'
      right_inv := fun y ↦ by
        apply Subtype.ext
        exact mul_div_cancel₀ y.val hd₀.ne'
      continuous_toFun := Continuous.subtype_mk
        (continuous_const.mul continuous_subtype_val) _
      continuous_invFun := Continuous.subtype_mk
        (continuous_subtype_val.div_const d) _ }
  let inc : Set.Ico (0 : ℝ) d → Set.Ico (0 : ℝ) 1 :=
    Set.inclusion (Set.Ico_subset_Ico_right hd₁)
  have hinc : Topology.IsOpenEmbedding inc := by
    apply Topology.IsOpenEmbedding.inclusion (Set.Ico_subset_Ico_right hd₁)
    have heq : (Subtype.val : Set.Ico (0 : ℝ) 1 → ℝ) ⁻¹' Set.Ico 0 d =
        (Subtype.val : Set.Ico (0 : ℝ) 1 → ℝ) ⁻¹' Set.Iio d := by
      ext x
      simp [x.property.1]
    rw [heq]
    exact isOpen_Iio.preimage continuous_subtype_val
  have hcomp := hinc.comp e.isOpenEmbedding
  have heq : inc ∘ e = collarScaleIco d hd₀ hd₁ := by
    funext x
    apply Subtype.ext
    rfl
  rwa [heq] at hcomp

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
