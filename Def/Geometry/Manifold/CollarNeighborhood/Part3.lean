/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Abbrev.Geometry.Manifold.CollarNeighborhood.Part3
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

/-- A manifold chart restricts to a homeomorphism from its boundary part to the zero face. -/
def collarBoundaryChart
    {n : ℕ} [NeZero n]
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) (⊤ : ℕ∞) M]
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace n))
    (he : e ∈ atlas (EuclideanHalfSpace n) M) :
    collarBoundaryChartSource e ≃ₜ collarBoundaryChartTarget e where
  toFun b := ⟨⟨e b.val.val, collarBoundaryCoordZeroOfChart he b.property b.val.property⟩,
    e.map_source b.property⟩
  invFun x := ⟨⟨e.symm x.val.val, by
    apply (collarMemBoundaryIffCoordZeroOfChart he (e.map_target x.property)).mpr
    rw [e.right_inv x.property]
    exact x.val.property⟩, e.map_target x.property⟩
  left_inv b := by
    apply Subtype.ext
    apply Subtype.ext
    exact e.left_inv b.property
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact e.right_inv x.property
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact e.continuousOn.comp_continuous
      (continuous_subtype_val.comp continuous_subtype_val) fun b ↦ b.property
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact e.symm.continuousOn.comp_continuous
      (continuous_subtype_val.comp continuous_subtype_val) fun x ↦ x.property

def collarBoundaryParamMap
    {n : ℕ} [NeZero n]
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) (⊤ : ℕ∞) M]
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace n))
    (he : e ∈ atlas (EuclideanHalfSpace n) M) (r : ℝ) :
    collarBoundaryChartSource e × Set.Ico (0 : ℝ) r → collarFace n × Set.Ico (0 : ℝ) r :=
  fun x ↦ (↑((collarBoundaryChart e he) x.1), x.2)

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
