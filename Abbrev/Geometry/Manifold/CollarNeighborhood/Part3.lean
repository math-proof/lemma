/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Theorem.Geometry.Manifold.CollarNeighborhood.Part2
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

abbrev collarBoundary
    {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M] :=
  ↥(ModelWithCorners.boundary (I := 𝓡∂ n) M)

abbrev collarBoundaryChartSource
    {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M]
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace n)) :=
  {b : collarBoundary (n := n) (M := M) // b.val ∈ e.source}

abbrev collarBoundaryChartTarget
    {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace n)) :=
  {x : collarFace n // x.val ∈ e.target}

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
