/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Def.Geometry.Manifold.CollarNeighborhood.Part37
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

theorem collarAnchor_zero
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (a : A) :
    collarAnchor g 0 a = collarExternalBase A a.val := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change -collarPartialWeight g 0 a = 0
    rw [collarPartialWeight_zero]
    norm_num

theorem collarExtendedChart_anchor
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (k m : ℕ) (a : A)
    (ha : a ∈ (g.data k).carrier) :
    collarExtendedChart (g.data k) (⟨a, ha⟩, collarPartialAnchor g m a) =
      collarAnchor g m a := by
  apply Subtype.ext
  rw [collarExtendedChart_val_of_nonpos (g.data k)
    (⟨a, ha⟩, collarPartialAnchor g m a)
    (by change -collarPartialWeight g m a ≤ 0
        linarith [collarPartialWeight_nonneg g m a])]
  rfl

theorem collarAnchor_not_mem_chartRange_of_not_mem
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (k m : ℕ) (a : A)
    (ha : a ∉ (g.data k).carrier) : collarAnchor g m a ∉ collarChartRange g k := by
  rintro ⟨z, hz⟩
  have hs : z.2.val ≤ 0 := by
    by_contra hs
    have hs' : 0 < z.2.val := lt_of_not_ge hs
    have hfirst := congrArg (fun y : collarExternal X A ↦ y.val.1) hz
    rw [collarExtendedChart_val_of_pos (g.data k) z hs'] at hfirst
    have hfirst' : (g.data k).map
        (z.1, ⟨z.2.val, hs'.le, z.2.property.2⟩) = a.val := by
      simpa [collarAnchor] using hfirst
    have hmem : (g.data k).map
        (z.1, ⟨z.2.val, hs'.le, z.2.property.2⟩) ∈ A := by
      rw [hfirst']
      exact a.property
    exact (g.data k).map_not_mem
      (z.1, ⟨z.2.val, hs'.le, z.2.property.2⟩) hs'
      hmem
  have hfirst := congrArg (fun y : collarExternal X A ↦ y.val.1) hz
  rw [collarExtendedChart_val_of_nonpos (g.data k) z hs] at hfirst
  apply ha
  have haz : z.1.val = a := by
    apply Subtype.ext
    exact hfirst
  rw [← haz]
  exact z.1.property

theorem collarGlobalPush_anchor
    {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) (k : ℕ) (a : A) :
    collarGlobalPush hA g k (collarAnchor g k a) = collarAnchor g (k + 1) a := by
  by_cases ha : a ∈ (g.data k).carrier
  · rw [← collarExtendedChart_anchor g k k a ha,
      collarGlobalPush_chart hA g k, collarChartPush_anchor g k ⟨a, ha⟩,
      collarExtendedChart_anchor g k (k + 1) a ha]
  · have hw : g.weight k a = 0 := by
      by_contra hw
      exact ha (g.subordinate k (subset_closure hw))
    rw [collarGlobalPush_eq_self_of_not_mem_range hA g k _
      (collarAnchor_not_mem_chartRange_of_not_mem g k k a ha)]
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change -collarPartialWeight g k a = -collarPartialWeight g (k + 1) a
      rw [collarPartialWeight_succ, hw, add_zero]

theorem collarPartialPush_anchor
    {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) (m : ℕ) (a : A) :
    collarPartialPush hA g m (collarExternalBase A a.val) = collarAnchor g m a := by
  induction m with
  | zero => exact (collarAnchor_zero g a).symm
  | succ k ih =>
      rw [collarPartialPush_succ_apply, ih, collarGlobalPush_anchor hA g k a]

theorem collarStripMap_zero
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (m : ℕ) (a : A)
    (hm : collarPartialWeight g m a = 1) :
    collarStripMap A (a, ⟨(0 : ℝ), by simp⟩) = collarAnchor g m a := by
  apply Subtype.ext
  rw [collarStripMap_val]
  apply Prod.ext
  · rfl
  · change (0 : ℝ) - 1 = -collarPartialWeight g m a
    rw [hm]
    ring

theorem collarGluedMap_zero
    {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) (a : A) :
    collarGluedMap hA g (a, ⟨(0 : ℝ), by simp⟩) = a.val := by
  let m := collarStageIndex g a
  let z : A × Set.Ico (0 : ℝ) 1 := (a, ⟨0, by simp⟩)
  have hm : collarPartialWeight g m a = 1 := collarStageIndex_spec g a
  have hrecover := collarFiniteMap_recover hA g m z hm
  have hglued : collarGluedMap hA g z = collarFiniteMap hA g m z :=
    collarGluedMap_eq_finite hA g m z hm
  have hanchor := collarPartialPush_anchor hA g m a
  rw [← collarStripMap_zero g m a hm, ← hrecover] at hanchor
  have hbase := (collarPartialPush hA g m).injective hanchor
  have hfst := congrArg (fun y : collarExternal X A ↦ y.val.1) hbase
  change a.val = collarFiniteMap hA g m z at hfst
  change collarGluedMap hA g z = a.val
  rw [hglued]
  exact hfst.symm

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
