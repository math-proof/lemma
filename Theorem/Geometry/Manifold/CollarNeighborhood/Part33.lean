/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Abbrev.Geometry.Manifold.CollarNeighborhood.Part13
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

theorem collarPushTube_isCompact
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (k : ℕ) : IsCompact (collarPushTube g k) :=
  (collarChartTubeDomain_isCompact g k).image
    (collarExtendedChart_continuous (g.data k))

theorem collarPushTube_isClosed
    {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X}
    (g : collarPreparedCover X A) (k : ℕ) : IsClosed (collarPushTube g k) :=
  (collarPushTube_isCompact g k).isClosed

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
