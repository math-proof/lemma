/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Def.Geometry.Manifold.CollarNeighborhood.Part30
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

theorem collarPushTube_subset_range
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (k : ℕ) :
    collarPushTube g k ⊆ collarChartRange g k := by
  rintro y ⟨z, hz, rfl⟩
  exact mem_range_self z

theorem collarRangePush_eq_self_of_not_mem_tube
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) (k : ℕ) (y : collarChartRange g k)
    (hy : y.val ∉ collarPushTube g k) : collarRangePushHomeomorph hA g k y = y := by
  let chart := collarExtendedChartHomeomorph hA (g.data k)
  let z := chart.symm y
  have hz : z ∉ collarChartTubeDomain g k := by
    intro hz
    apply hy
    refine ⟨z, hz, ?_⟩
    exact congrArg Subtype.val (chart.apply_symm_apply y)
  change chart (collarChartPush g k z) = y
  rw [collarChartPush_eq_self_of_not_mem_tube g k z hz]
  exact chart.apply_symm_apply y

theorem collarRangePush_symm_eq_self_of_not_mem_tube
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) (k : ℕ) (y : collarChartRange g k)
    (hy : y.val ∉ collarPushTube g k) :
    (collarRangePushHomeomorph hA g k).symm y = y := by
  let chart := collarExtendedChartHomeomorph hA (g.data k)
  let z := chart.symm y
  have hz : z ∉ collarChartTubeDomain g k := by
    intro hz
    apply hy
    refine ⟨z, hz, ?_⟩
    exact congrArg Subtype.val (chart.apply_symm_apply y)
  change chart (collarChartPushInv g k z) = y
  rw [collarChartPushInv_eq_self_of_not_mem_tube g k z hz]
  exact chart.apply_symm_apply y

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
