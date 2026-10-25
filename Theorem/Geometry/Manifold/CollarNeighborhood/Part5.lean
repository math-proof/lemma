/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Abbrev.Geometry.Manifold.CollarNeighborhood.Part6
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

theorem collarExternal_fst_mem_of_snd_lt
    {X : Type*} [TopologicalSpace X] {A : Set X} (y : collarExternal X A)
    (hy : y.val.2 < 0) : y.val.1 ∈ A := by
  rcases y.property with hy0 | hyA
  · exfalso
    have hz : y.val.2 = 0 := hy0.2
    rw [hz] at hy
    exact (lt_irrefl 0 hy).elim
  · exact hyA.1

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
