module
public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Topology.LocalAtTarget
public import Mathlib.Topology.PartitionOfUnity
public import Theorem.Geometry.Manifold.CollarNeighborhood.Part36


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

abbrev collarStage
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (m : ℕ) : Set (collarExternal X A) :=
  {y | y.val.2 = 0 ∨ ∃ ha : y.val.1 ∈ A,
    -collarPartialWeight g m (⟨y.val.1, ha⟩ : A) ≤ y.val.2}

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
