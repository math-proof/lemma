/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Def.Geometry.Manifold.CollarNeighborhood.Part27
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

theorem collarChartPush_anchor
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (k : ℕ) (a : (g.data k).carrier) :
    collarChartPush g k (a, collarPartialAnchor g k a.val) =
      (a, collarPartialAnchor g (k + 1) a.val) := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    exact collarFiberMap_anchor (collarChartPushParameters g k a).1
      (collarChartPushParameters g k a).2

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
