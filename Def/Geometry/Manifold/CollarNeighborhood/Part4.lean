/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Abbrev.Geometry.Manifold.CollarNeighborhood.Part4
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

def collarLocalMap
    {n : ℕ} [NeZero n]
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) (⊤ : ℕ∞) M]
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace n))
    (he : e ∈ atlas (EuclideanHalfSpace n) M) (r : ℝ) :
    ↥(collarLocalDomain e he r) → M :=
  fun x ↦ collarChartMap e r ⟨collarBoundaryParamMap e he r x.val, x.property⟩

def collarLocalZeroPoint
    {n : ℕ} [NeZero n]
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) (⊤ : ℕ∞) M]
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace n))
    (he : e ∈ atlas (EuclideanHalfSpace n) M) (r : ℝ) (hr : 0 < r)
    (b : collarBoundaryChartSource e) : ↥(collarLocalDomain e he r) :=
  ⟨(b, ⟨0, ⟨le_rfl, hr⟩⟩), by
    change collarModelMap n r
      (↑((collarBoundaryChart e he) b), ⟨0, by exact ⟨le_rfl, hr⟩⟩) ∈ e.target
    rw [collarModelMap_zero n hr]
    exact e.map_source b.property⟩

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
