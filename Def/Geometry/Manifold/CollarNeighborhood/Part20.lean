/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Abbrev.Geometry.Manifold.CollarNeighborhood.Part8
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

/-- The piecewise-linear fibre map used to push one partial collar to the next. -/
def collarFiberMap (p q s : ℝ) : ℝ :=
  if s ≤ -p then
    -2 + (s + 2) * (2 - q) / (2 - p)
  else if s ≤ (1 / 2 : ℝ) then
    -q + (s + p) * (q + 1 / 2) / (p + 1 / 2)
  else s

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
