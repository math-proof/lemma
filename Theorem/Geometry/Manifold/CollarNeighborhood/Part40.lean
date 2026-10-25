/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Def.Geometry.Manifold.CollarNeighborhood.Part34
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

theorem collarFiniteMap_lift
    {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) (m : ℕ) (z : A × Set.Ico (0 : ℝ) 1)
    (hm : collarPartialWeight g m z.1 = 1) :
    collarExternalBase A (collarFiniteMap hA g m z) =
      (collarPartialPush hA g m).symm (collarStripMap A z) := by
  have hj : collarStripMap A z ∈ collarStage g m := collarStripMap_mem_stage g m z hm
  rw [← collarPartialPush_image_base hA g m] at hj
  rcases hj with ⟨y, ⟨x, rfl⟩, hy⟩
  have hinv : (collarPartialPush hA g m).symm (collarStripMap A z) =
      collarExternalBase A x := by
    rw [← hy]
    simp
  change collarExternalBase A
    (((collarPartialPush hA g m).symm (collarStripMap A z)).val.1) =
      (collarPartialPush hA g m).symm (collarStripMap A z)
  rw [hinv]
  rfl

theorem collarFiniteMap_recover
    {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) (m : ℕ) (z : A × Set.Ico (0 : ℝ) 1)
    (hm : collarPartialWeight g m z.1 = 1) :
    collarPartialPush hA g m (collarExternalBase A (collarFiniteMap hA g m z)) =
      collarStripMap A z := by
  rw [collarFiniteMap_lift hA g m z hm]
  simp

theorem collarWeight_eq_zero_of_partial_eq_one
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (a : A) {m k : ℕ}
    (hm : collarPartialWeight g m a = 1) (hmk : m ≤ k) : g.weight k a = 0 := by
  have hk : collarPartialWeight g k a = 1 := by
    apply le_antisymm (collarPartialWeight_le_one g k a)
    rw [← hm]
    exact collarPartialWeight_mono_of_le g a hmk
  have hsucc := collarPartialWeight_le_one g (k + 1) a
  rw [collarPartialWeight_succ, hk] at hsucc
  exact le_antisymm (by linarith) (g.weight.nonneg k a)

theorem collarStripMap_not_mem_chartRange_of_not_mem
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (k : ℕ) (z : A × Set.Ico (0 : ℝ) 1)
    (ha : z.1 ∉ (g.data k).carrier) : collarStripMap A z ∉ collarChartRange g k := by
  rintro ⟨w, hw⟩
  have hsneg : (collarStripMap A z).val.2 < 0 := by
    rw [collarStripMap_val]
    linarith [z.2.property.2]
  have hwneg : w.2.val < 0 := by
    by_contra h
    have hw0 : (collarExtendedChart (g.data k) w).val.2 = 0 := by
      rw [collarExtendedChart_val_of_nonneg (g.data k) w (le_of_not_gt h)]
    have := congrArg (fun y : collarExternal X A ↦ y.val.2) hw
    linarith
  have hfirst := congrArg (fun y : collarExternal X A ↦ y.val.1) hw
  rw [collarExtendedChart_val_of_nonpos (g.data k) w hwneg.le,
    collarStripMap_val] at hfirst
  apply ha
  have hza : w.1.val = z.1 := by
    apply Subtype.ext
    exact hfirst
  rw [← hza]
  exact w.1.property

theorem collarGlobalPush_strip_eq_self_of_weight_eq_zero
    {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) (k : ℕ) (z : A × Set.Ico (0 : ℝ) 1)
    (hw : g.weight k z.1 = 0) :
    collarGlobalPush hA g k (collarStripMap A z) = collarStripMap A z := by
  by_cases ha : z.1 ∈ (g.data k).carrier
  · let s : Set.Ico (-2 : ℝ) 1 :=
      ⟨z.2.val - 1, by linarith [z.2.property.1], by linarith [z.2.property.2]⟩
    let w : (g.data k).carrier × Set.Ico (-2 : ℝ) 1 := (⟨z.1, ha⟩, s)
    have hchart : collarExtendedChart (g.data k) w = collarStripMap A z := by
      apply Subtype.ext
      rw [collarExtendedChart_val_of_nonpos (g.data k) w
        (by dsimp [w, s]; linarith [z.2.property.2]), collarStripMap_val]
    rw [← hchart, collarGlobalPush_chart hA g k,
      collarChartPush_eq_self_of_weight_eq_zero g k w]
    exact hw
  · exact collarGlobalPush_eq_self_of_not_mem_range hA g k _
      (collarStripMap_not_mem_chartRange_of_not_mem g k z ha)

theorem collarGlobalPush_symm_strip_eq_self_of_weight_eq_zero
    {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) (k : ℕ) (z : A × Set.Ico (0 : ℝ) 1)
    (hw : g.weight k z.1 = 0) :
    (collarGlobalPush hA g k).symm (collarStripMap A z) = collarStripMap A z := by
  apply (collarGlobalPush hA g k).injective
  rw [(collarGlobalPush hA g k).apply_symm_apply]
  exact (collarGlobalPush_strip_eq_self_of_weight_eq_zero hA g k z hw).symm

theorem collarPartialPush_symm_strip_stable
    {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) (z : A × Set.Ico (0 : ℝ) 1) {m n : ℕ}
    (hm : collarPartialWeight g m z.1 = 1) (hmn : m ≤ n) :
    (collarPartialPush hA g n).symm (collarStripMap A z) =
      (collarPartialPush hA g m).symm (collarStripMap A z) := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
      change (collarPartialPush hA g n).symm
        ((collarGlobalPush hA g n).symm (collarStripMap A z)) = _
      rw [collarGlobalPush_symm_strip_eq_self_of_weight_eq_zero hA g n z
        (collarWeight_eq_zero_of_partial_eq_one g z.1 hm hmn)]
      exact ih

theorem collarFiniteMap_eq_of_partial_eq_one
    {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) (z : A × Set.Ico (0 : ℝ) 1) {m n : ℕ}
    (hm : collarPartialWeight g m z.1 = 1) (hn : collarPartialWeight g n z.1 = 1) :
    collarFiniteMap hA g m z = collarFiniteMap hA g n z := by
  let k := max m n
  have hmk : m ≤ k := le_max_left _ _
  have hnk : n ≤ k := le_max_right _ _
  have hmstable := collarPartialPush_symm_strip_stable hA g z hm hmk
  have hnstable := collarPartialPush_symm_strip_stable hA g z hn hnk
  exact congrArg (fun y : collarExternal X A ↦ y.val.1) (hmstable.symm.trans hnstable)

theorem collarPartialWeight_eq_one_of_le
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (a : A) {m k : ℕ}
    (hm : collarPartialWeight g m a = 1) (hmk : m ≤ k) :
    collarPartialWeight g k a = 1 := by
  apply le_antisymm (collarPartialWeight_le_one g k a)
  rw [← hm]
  exact collarPartialWeight_mono_of_le g a hmk

theorem collarExistsPartialWeightEqOne
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (a : A) :
    ∃ m, collarPartialWeight g m a = 1 := by
  obtain ⟨m, hm⟩ := collarPartialWeight_eventually_eq_one g a
  exact ⟨m, hm.eq_of_nhds⟩

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
