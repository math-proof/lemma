/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Def.Geometry.Manifold.CollarNeighborhood.Part14
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

theorem collarExtendedNegative_continuous
    {X : Type*} [TopologicalSpace X] {A : Set X} (d : collarLocalData X A) :
    Continuous (collarExtendedNegative d) := by
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst)).prodMk
    ((continuous_subtype_val.comp continuous_snd).min continuous_const)

theorem collarExtendedPositive_continuous
    {X : Type*} [TopologicalSpace X] {A : Set X} (d : collarLocalData X A) :
    Continuous (collarExtendedPositive d) := by
  apply collarExternalBase_continuous.comp
  apply d.isOpenEmbedding_map.continuous.comp
  exact continuous_fst.prodMk <| Continuous.subtype_mk
    (continuous_const.max (continuous_subtype_val.comp continuous_snd)) _

theorem collarExtendedChart_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} (d : collarLocalData X A)
    (z : d.carrier × Set.Ico (-2 : ℝ) 1) :
    collarExtendedChart d z = if z.2.val ≤ 0 then
      collarExtendedNegative d z else collarExtendedPositive d z := by
  by_cases hz : z.2.val ≤ 0
  · rw [ite_eq_left hz]
    apply Subtype.ext
    rw [collarExtendedChart_val_of_nonpos d z hz]
    simp [collarExtendedNegative, min_eq_left hz]
  · rw [ite_eq_right hz]
    have hz' : 0 < z.2.val := lt_of_not_ge hz
    apply Subtype.ext
    rw [collarExtendedChart_val_of_pos d z hz']
    simp [collarExtendedPositive, collarExternalBase, max_eq_right hz'.le]

theorem collarExtendedChart_continuous
    {X : Type*} [TopologicalSpace X] {A : Set X} (d : collarLocalData X A) :
    Continuous (collarExtendedChart d) := by
  rw [show collarExtendedChart d = fun z ↦ if z.2.val ≤ 0 then
    collarExtendedNegative d z else collarExtendedPositive d z from
      funext (collarExtendedChart_eq d)]
  exact Continuous.if_le (collarExtendedNegative_continuous d)
    (collarExtendedPositive_continuous d) (continuous_subtype_val.comp continuous_snd)
    continuous_const fun z hz ↦ by
      apply Subtype.ext
      change (z.1.val.val, min z.2.val 0) =
        (d.map (z.1, ⟨max 0 z.2.val, by simp [z.2.property.2]⟩), 0)
      have hmin : min z.2.val 0 = 0 := by simp [hz]
      have hmax : (⟨max 0 z.2.val, by simp [z.2.property.2]⟩ : Set.Ico (0 : ℝ) 1) =
          ⟨0, by simp⟩ := by
        apply Subtype.ext
        simp [hz]
      rw [hmin, hmax, d.map_zero z.1]

theorem collarExtendedChart_injective
    {X : Type*} [TopologicalSpace X] {A : Set X} (d : collarLocalData X A) :
    Function.Injective (collarExtendedChart d) := by
  intro z w hzw
  by_cases hz : z.2.val ≤ 0 <;> by_cases hw : w.2.val ≤ 0
  · have hval := congrArg Subtype.val hzw
    rw [collarExtendedChart_val_of_nonpos d z hz,
      collarExtendedChart_val_of_nonpos d w hw] at hval
    apply Prod.ext
    · apply Subtype.ext
      apply Subtype.ext
      exact congrArg Prod.fst hval
    · apply Subtype.ext
      exact congrArg Prod.snd hval
  · have hw' : 0 < w.2.val := lt_of_not_ge hw
    have hval := congrArg Subtype.val hzw
    rw [collarExtendedChart_val_of_nonpos d z hz,
      collarExtendedChart_val_of_pos d w hw'] at hval
    have hfst : z.1.val.val =
        d.map (w.1, ⟨w.2.val, hw'.le, w.2.property.2⟩) := congrArg Prod.fst hval
    have hmem : d.map (w.1, ⟨w.2.val, hw'.le, w.2.property.2⟩) ∈ A := by
      exact (congrArg (fun x : X ↦ x ∈ A) hfst).mp z.1.val.property
    exact (d.map_not_mem _ hw' hmem).elim
  · have hz' : 0 < z.2.val := lt_of_not_ge hz
    have hval := congrArg Subtype.val hzw
    rw [collarExtendedChart_val_of_pos d z hz',
      collarExtendedChart_val_of_nonpos d w hw] at hval
    have hfst : d.map (z.1, ⟨z.2.val, hz'.le, z.2.property.2⟩) =
        w.1.val.val := congrArg Prod.fst hval
    have hmem : d.map (z.1, ⟨z.2.val, hz'.le, z.2.property.2⟩) ∈ A := by
      exact (congrArg (fun x : X ↦ x ∈ A) hfst).mpr w.1.val.property
    exact (d.map_not_mem _ hz' hmem).elim
  · have hz' : 0 < z.2.val := lt_of_not_ge hz
    have hw' : 0 < w.2.val := lt_of_not_ge hw
    have hval := congrArg Subtype.val hzw
    rw [collarExtendedChart_val_of_pos d z hz',
      collarExtendedChart_val_of_pos d w hw'] at hval
    have hmap := d.isOpenEmbedding_map.injective (congrArg Prod.fst hval)
    apply Prod.ext
    · exact congrArg (fun p : d.carrier × Set.Ico (0 : ℝ) 1 ↦ p.1) hmap
    · apply Subtype.ext
      exact congrArg (fun p : d.carrier × Set.Ico (0 : ℝ) 1 ↦ p.2.val) hmap

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
