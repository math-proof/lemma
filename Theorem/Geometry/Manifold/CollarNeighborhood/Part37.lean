/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Abbrev.Geometry.Manifold.CollarNeighborhood.Part15
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

theorem collarExternalBase_range
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    range (collarExternalBase A) = {y : collarExternal X A | y.val.2 = 0} := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    rfl
  · intro hy
    refine ⟨y.val.1, ?_⟩
    apply Subtype.ext
    exact Prod.ext rfl hy.symm

theorem collarStage_zero
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) :
    collarStage g 0 = range (collarExternalBase A) := by
  rw [collarExternalBase_range]
  ext y
  constructor
  · rintro (hy | ⟨ha, hy⟩)
    · exact hy
    · have hnonpos : y.val.2 ≤ 0 := by
        rcases y.property with hy0 | hyA
        · exact hy0.2.le
        · exact hyA.2.2
      rw [collarPartialWeight_zero] at hy
      exact le_antisymm hnonpos (by simpa using hy)
  · exact Or.inl

theorem collarExtendedChart_mem_stage_iff
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (k m : ℕ)
    (z : (g.data k).carrier × Set.Ico (-2 : ℝ) 1) :
    collarExtendedChart (g.data k) z ∈ collarStage g m ↔
      -collarPartialWeight g m z.1.val ≤ z.2.val := by
  change ((collarExtendedChart (g.data k) z).val.2 = 0 ∨
    ∃ ha : (collarExtendedChart (g.data k) z).val.1 ∈ A,
      -collarPartialWeight g m
        (⟨(collarExtendedChart (g.data k) z).val.1, ha⟩ : A) ≤
          (collarExtendedChart (g.data k) z).val.2) ↔
    -collarPartialWeight g m z.1.val ≤ z.2.val
  by_cases hs : z.2.val ≤ 0
  · rw [collarExtendedChart_val_of_nonpos (g.data k) z hs]
    constructor
    · rintro (hz | ⟨ha, ha'⟩)
      · have hz' : z.2.val = 0 := by simpa only [Prod.snd] using hz
        rw [hz']
        linarith [collarPartialWeight_nonneg g m z.1.val]
      · have hsame : (⟨z.1.val.val, ha⟩ : A) = z.1.val := by
          apply Subtype.ext
          rfl
        simpa [hsame] using ha'
    · intro hz
      exact Or.inr ⟨z.1.val.property, hz⟩
  · have hs' : 0 < z.2.val := lt_of_not_ge hs
    rw [collarExtendedChart_val_of_pos (g.data k) z hs']
    constructor
    · intro _
      linarith [collarPartialWeight_nonneg g m z.1.val]
    · intro _
      exact Or.inl rfl

theorem collarGlobalPush_eq_self_of_not_mem_range
    {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) (k : ℕ) (y : collarExternal X A)
    (hy : y ∉ collarChartRange g k) : collarGlobalPush hA g k y = y := by
  change collarExtendByIdentityFun (collarChartRange g k)
    (collarRangePushHomeomorph hA g k) y = y
  simp [collarExtendByIdentityFun, hy]

theorem collarWeight_eq_zero_of_external_not_mem_range
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (k : ℕ) (y : collarExternal X A)
    (hyneg : y.val.2 < 0) (hy : y ∉ collarChartRange g k) :
    g.weight k (⟨y.val.1, collarExternal_fst_mem_of_snd_lt y hyneg⟩ : A) = 0 := by
  let a : A := ⟨y.val.1, collarExternal_fst_mem_of_snd_lt y hyneg⟩
  by_contra hw
  have ha : a ∈ (g.data k).carrier := g.subordinate k (subset_closure hw)
  have hlow : -2 ≤ y.val.2 := by
    rcases y.property with hy0 | hyA
    · rw [hy0.2]
      norm_num
    · exact hyA.2.1
  let z : (g.data k).carrier × Set.Ico (-2 : ℝ) 1 :=
    (⟨a, ha⟩, ⟨y.val.2, hlow, hyneg.trans (by norm_num)⟩)
  apply hy
  refine ⟨z, ?_⟩
  apply Subtype.ext
  rw [collarExtendedChart_val_of_nonpos (g.data k) z hyneg.le]

theorem collarStage_succ_iff_of_not_mem_range
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (k : ℕ) (y : collarExternal X A)
    (hy : y ∉ collarChartRange g k) : y ∈ collarStage g (k + 1) ↔ y ∈ collarStage g k := by
  by_cases hy0 : y.val.2 = 0
  · exact iff_of_true (Or.inl hy0) (Or.inl hy0)
  have hyneg : y.val.2 < 0 := by
    rcases y.property with hbase | hstrip
    · exact (hy0 hbase.2).elim
    · exact lt_of_le_of_ne hstrip.2.2 hy0
  have hw := collarWeight_eq_zero_of_external_not_mem_range g k y hyneg hy
  have hsum (ha : y.val.1 ∈ A) :
      collarPartialWeight g (k + 1) (⟨y.val.1, ha⟩ : A) =
        collarPartialWeight g k (⟨y.val.1, ha⟩ : A) := by
    rw [collarPartialWeight_succ]
    have haa : (⟨y.val.1, ha⟩ : A) =
        ⟨y.val.1, collarExternal_fst_mem_of_snd_lt y hyneg⟩ := by
      apply Subtype.ext
      rfl
    rw [haa, hw, add_zero]
  constructor
  · rintro (_ | ⟨ha, h⟩)
    · exact (hy0 ‹y.val.2 = 0›).elim
    · exact Or.inr ⟨ha, by simpa [hsum ha] using h⟩
  · rintro (_ | ⟨ha, h⟩)
    · exact (hy0 ‹y.val.2 = 0›).elim
    · exact Or.inr ⟨ha, by simpa [hsum ha] using h⟩

theorem collarGlobalPush_mem_stage_iff
    {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) (k : ℕ) (y : collarExternal X A) :
    collarGlobalPush hA g k y ∈ collarStage g (k + 1) ↔ y ∈ collarStage g k := by
  by_cases hy : y ∈ collarChartRange g k
  · rcases hy with ⟨z, rfl⟩
    rw [collarGlobalPush_chart hA g k,
      collarExtendedChart_mem_stage_iff g k (k + 1),
      collarExtendedChart_mem_stage_iff g k k]
    exact collarFiberMap_ge_anchor_iff
      (collarPartialWeightIcc g k z.1.val)
      (collarPartialWeightIcc g (k + 1) z.1.val) z.2
  · rw [collarGlobalPush_eq_self_of_not_mem_range hA g k y hy]
    exact collarStage_succ_iff_of_not_mem_range g k y hy

theorem collarGlobalPush_image_stage
    {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) (k : ℕ) :
    collarGlobalPush hA g k '' collarStage g k = collarStage g (k + 1) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (collarGlobalPush_mem_stage_iff hA g k x).2 hx
  · intro hy
    let x := (collarGlobalPush hA g k).symm y
    have hx : x ∈ collarStage g k := by
      apply (collarGlobalPush_mem_stage_iff hA g k x).1
      simpa [x] using hy
    exact ⟨x, hx, by simp [x]⟩

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
