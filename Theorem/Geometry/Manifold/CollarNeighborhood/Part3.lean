/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Def.Geometry.Manifold.CollarNeighborhood.Part4
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

/-- Every point of the boundary chart is fixed by the local collar at normal coordinate zero. -/
theorem collarLocalMap_zero
    {n : ℕ} [NeZero n]
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) (⊤ : ℕ∞) M]
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace n))
    (he : e ∈ atlas (EuclideanHalfSpace n) M) (r : ℝ) (hr : 0 < r)
    (b : collarBoundaryChartSource e) :
    collarLocalMap e he r (collarLocalZeroPoint e he r hr b) = b.val.val := by
  change e.symm (collarModelMap n r
    (↑((collarBoundaryChart e he) b), ⟨0, by exact ⟨le_rfl, hr⟩⟩)) = b.val.val
  rw [collarModelMap_zero n hr]
  exact e.left_inv b.property

/-- Positive normal parameters in a chart collar lie off the manifold boundary. -/
theorem collarLocalMap_not_mem_boundary
    {n : ℕ} [NeZero n]
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) (⊤ : ℕ∞) M]
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace n))
    (he : e ∈ atlas (EuclideanHalfSpace n) M) (r : ℝ)
    (z : ↥(collarLocalDomain e he r)) (hz : 0 < z.val.2.val) :
    collarLocalMap e he r z ∉ ModelWithCorners.boundary (I := 𝓡∂ n) M := by
  intro hb
  have hsource : collarLocalMap e he r z ∈ e.source := by
    exact e.map_target z.property
  have hzero := (collarMemBoundaryIffCoordZeroOfChart he hsource).mp hb
  change (e (e.symm (collarModelMap n r (collarBoundaryParamMap e he r z.val)))).val 0 = 0
    at hzero
  rw [e.right_inv z.property] at hzero
  change
    ((collarHalfSpaceSplit n).symm
      (↑((collarBoundaryChart e he) z.val.1), collarIcoToIci r z.val.2)).val 0 = 0 at hzero
  simpa [collarHalfSpaceSplit, collarIcoToIci] using hz.ne' hzero

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
