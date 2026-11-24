module
public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Topology.LocalAtTarget
public import Mathlib.Topology.PartitionOfUnity
public import Theorem.Geometry.Manifold.CollarNeighborhood.Part44


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

def collarFiniteMapOn
    {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) (m : ℕ) (W : Set A) :
    W × Set.Ico (0 : ℝ) 1 → X :=
  fun z ↦ collarFiniteMap hA g m (z.1.val, z.2)

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
