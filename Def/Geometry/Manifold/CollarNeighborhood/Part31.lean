/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Theorem.Geometry.Manifold.CollarNeighborhood.Part35
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

def collarGlobalPush
    {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) (k : ℕ) :
    collarExternal X A ≃ₜ collarExternal X A :=
  collarExtendByIdentity (collarChartRange g k) (collarPushTube g k)
    (collarRangePushHomeomorph hA g k) (collarChartRange_isOpen hA g k)
    (collarPushTube_isClosed g k) (collarPushTube_subset_range g k)
    (collarRangePush_eq_self_of_not_mem_tube hA g k)
    (collarRangePush_symm_eq_self_of_not_mem_tube hA g k)

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
