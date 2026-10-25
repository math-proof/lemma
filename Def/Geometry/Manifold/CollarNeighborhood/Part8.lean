/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Theorem.Geometry.Manifold.CollarNeighborhood.Part8
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

def collarNegativeIntervalInclusion :
    Set.Ico (-2 : ℝ) 0 → Set.Ico (-2 : ℝ) 1 :=
  Set.inclusion fun _ hx ↦ ⟨hx.1, hx.2.trans (by norm_num)⟩

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
