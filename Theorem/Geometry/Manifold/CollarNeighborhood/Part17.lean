module
public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Topology.LocalAtTarget
public import Mathlib.Topology.PartitionOfUnity
public import Def.Geometry.Manifold.CollarNeighborhood.Part16


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/
noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

theorem collarExtendedPositiveInclusion_isOpenEmbedding
    {X : Type*} [TopologicalSpace X] {A : Set X} (d : collarLocalData X A) :
    Topology.IsOpenEmbedding (collarExtendedPositiveInclusion d) := by
  exact Topology.IsOpenEmbedding.id.prodMap
    collarPositiveExtendedIntervalInclusion_isOpenEmbedding

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
