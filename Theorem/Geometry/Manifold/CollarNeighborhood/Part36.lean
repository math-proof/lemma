/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Def.Geometry.Manifold.CollarNeighborhood.Part31
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

theorem collarGlobalPush_chart
    {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) (k : ℕ)
    (z : (g.data k).carrier × Set.Ico (-2 : ℝ) 1) :
    collarGlobalPush hA g k (collarExtendedChart (g.data k) z) =
      collarExtendedChart (g.data k) (collarChartPush g k z) := by
  let chart := collarExtendedChartHomeomorph hA (g.data k)
  have hy : collarExtendedChart (g.data k) z ∈ collarChartRange g k := mem_range_self z
  rw [show collarGlobalPush hA g k (collarExtendedChart (g.data k) z) =
      ((collarRangePushHomeomorph hA g k)
        ⟨collarExtendedChart (g.data k) z, hy⟩).val by
    exact collarExtendByIdentityFun_apply_mem _ _ hy]
  change (chart (collarChartPush g k (chart.symm ⟨collarExtendedChart (g.data k) z, hy⟩))).val = _
  have hz : chart.symm ⟨collarExtendedChart (g.data k) z, hy⟩ = z := by
    have hyz : (⟨collarExtendedChart (g.data k) z, hy⟩ : collarChartRange g k) =
        chart z := by
      apply Subtype.ext
      rfl
    rw [hyz, chart.symm_apply_apply]
  rw [hz]
  rfl

theorem collarFiberMap_ge_anchor_iff
    (p q : Set.Icc (0 : ℝ) 1) (s : Set.Ico (-2 : ℝ) 1) :
    -q.val ≤ collarFiberMap p.val q.val s.val ↔ -p.val ≤ s.val := by
  constructor
  · intro h
    by_contra hs
    have hsp : s.val < -p.val := lt_of_not_ge hs
    rw [collarFiberMap_lower hsp.le] at h
    have hp : 0 < 2 - p.val := collarFiberDenomTwoPos p
    have hq : 0 < 2 - q.val := by linarith [q.property.2]
    have hs' : s.val + 2 < 2 - p.val := by linarith
    have hmul := mul_lt_mul_of_pos_right hs' hq
    have hdiv : (s.val + 2) * (2 - q.val) / (2 - p.val) < 2 - q.val := by
      apply (div_lt_iff₀ hp).2
      simpa [mul_comm] using hmul
    linarith
  · intro h
    rcases h.eq_or_lt with h | h
    · rw [← h, collarFiberMap_anchor p q]
    · by_cases hs : s.val ≤ (1 / 2 : ℝ)
      · exact (collarFiberMap_middle_bounds p q h hs).1.le
      · rw [collarFiberMap_upper p hs]
        linarith [q.property.1]

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
