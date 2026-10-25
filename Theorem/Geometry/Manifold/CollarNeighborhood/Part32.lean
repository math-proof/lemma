/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Abbrev.Geometry.Manifold.CollarNeighborhood.Part12
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

theorem collarChartTubeDomain_isCompact
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (k : ℕ) : IsCompact (collarChartTubeDomain g k) :=
  (collarChartSupport_isCompact g k).prod collarLowerHalf_isCompact

theorem collarChartPush_eq_self_of_not_mem_tube
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (k : ℕ)
    (z : (g.data k).carrier × Set.Ico (-2 : ℝ) 1)
    (hz : z ∉ collarChartTubeDomain g k) : collarChartPush g k z = z := by
  by_cases ha : z.1.val ∈ tsupport (g.weight k)
  · have hs : (1 / 2 : ℝ) < z.2.val := by
      by_contra hs
      exact hz ⟨ha, le_of_not_gt hs⟩
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact collarFiberMap_upper (collarChartPushParameters g k z.1).1
        (not_le_of_gt hs)
  · have hw : g.weight k z.1.val = 0 := by
      by_contra hw
      exact ha (subset_closure hw)
    exact collarChartPush_eq_self_of_weight_eq_zero g k z hw

theorem collarChartPushInv_eq_self_of_not_mem_tube
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (k : ℕ)
    (z : (g.data k).carrier × Set.Ico (-2 : ℝ) 1)
    (hz : z ∉ collarChartTubeDomain g k) : collarChartPushInv g k z = z := by
  by_cases ha : z.1.val ∈ tsupport (g.weight k)
  · have hs : (1 / 2 : ℝ) < z.2.val := by
      by_contra hs
      exact hz ⟨ha, le_of_not_gt hs⟩
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact collarFiberMap_upper (collarChartPushParameters g k z.1).2
        (not_le_of_gt hs)
  · have hw : g.weight k z.1.val = 0 := by
      by_contra hw
      exact ha (subset_closure hw)
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      have hpq : (collarChartPushParameters g k z.1).1 =
          (collarChartPushParameters g k z.1).2 := by
        apply Subtype.ext
        change collarPartialWeight g k z.1.val = collarPartialWeight g (k + 1) z.1.val
        rw [collarPartialWeight_succ, hw, add_zero]
      change collarFiberMap (collarChartPushParameters g k z.1).2.val
        (collarChartPushParameters g k z.1).1.val z.2.val = z.2.val
      rw [hpq]
      exact collarFiberMap_self (collarChartPushParameters g k z.1).2 z.2

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
