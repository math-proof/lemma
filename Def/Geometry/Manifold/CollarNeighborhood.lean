/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Abbrev.Geometry.Manifold.CollarNeighborhood
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

/-- Splitting a Euclidean half-space into its boundary face and normal coordinate. -/
def collarHalfSpaceSplit (n : ℕ) [NeZero n] :
    EuclideanHalfSpace n ≃ₜ collarFace n × Set.Ici (0 : ℝ) where
  toFun x :=
    (⟨⟨toLp 2 (Function.update x.val 0 0), by simp⟩, by simp⟩,
      ⟨x.val 0, x.property⟩)
  invFun x :=
    ⟨toLp 2 (Function.update x.1.val.val 0 x.2.val), by
      rw [PiLp.toLp_apply, Function.update_self]
      exact x.2.property⟩
  left_inv x := by
    apply EuclideanHalfSpace.ext
    apply PiLp.ext
    intro i
    by_cases hi : i = 0
    · subst i
      simp
    · simp [hi]
  right_inv x := by
    apply Prod.ext
    · apply Subtype.ext
      apply EuclideanHalfSpace.ext
      apply PiLp.ext
      intro i
      by_cases hi : i = 0
      · subst i
        simp [x.1.property]
      · simp [hi]
    · apply Subtype.ext
      simp
  continuous_toFun := by
    fun_prop
  continuous_invFun := by
    fun_prop

def collarIcoToIci (r : ℝ) : Set.Ico (0 : ℝ) r → Set.Ici (0 : ℝ) :=
  Set.inclusion Set.Ico_subset_Ici_self

def collarModelMap (n : ℕ) [NeZero n] (r : ℝ) :
    collarFace n × Set.Ico (0 : ℝ) r → EuclideanHalfSpace n :=
  (collarHalfSpaceSplit n).symm ∘ Prod.map id (collarIcoToIci r)

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
