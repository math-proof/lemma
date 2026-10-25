/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Def.Geometry.Manifold.CollarNeighborhood.Part26
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

theorem collarChartPush_eq_self_of_weight_eq_zero
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (k : ℕ)
    (z : (g.data k).carrier × Set.Ico (-2 : ℝ) 1)
    (hz : g.weight k z.1.val = 0) : collarChartPush g k z = z := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    have hpq : (collarChartPushParameters g k z.1).1 =
        (collarChartPushParameters g k z.1).2 := by
      apply Subtype.ext
      change collarPartialWeight g k z.1.val = collarPartialWeight g (k + 1) z.1.val
      rw [collarPartialWeight_succ, hz, add_zero]
    change collarFiberMap (collarChartPushParameters g k z.1).1.val
      (collarChartPushParameters g k z.1).2.val z.2.val = z.2.val
    rw [← hpq]
    exact collarFiberMap_self (collarChartPushParameters g k z.1).1 z.2

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
