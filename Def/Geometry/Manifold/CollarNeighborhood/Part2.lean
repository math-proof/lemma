/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Abbrev.Geometry.Manifold.CollarNeighborhood.Part2
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

def collarChartMap {n : ℕ} {M : Type*} [TopologicalSpace M] [NeZero n]
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace n)) (r : ℝ) :
    ↥(collarChartDomain e r) → M :=
  fun x => e.symm (collarModelMap n r x.val)

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
