/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Theorem.Geometry.Manifold.CollarNeighborhood.Part11
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

structure collarLocalData
    (X : Type*) [TopologicalSpace X] (A : Set X) where
  carrier : Set A
  isOpen_carrier : IsOpen carrier
  map : carrier × Set.Ico (0 : ℝ) 1 → X
  isOpenEmbedding_map : Topology.IsOpenEmbedding map
  map_zero : ∀ u : carrier, map (u, ⟨0, by simp⟩) = u.val.val
  map_not_mem : ∀ z, 0 < z.2.val → map z ∉ A

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
