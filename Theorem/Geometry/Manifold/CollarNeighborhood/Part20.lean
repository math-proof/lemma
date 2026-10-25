/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Def.Geometry.Manifold.CollarNeighborhood.Part19
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

theorem collarExtendedPositivePart_isOpenEmbedding
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A)
    (d : collarLocalData X A) : Topology.IsOpenEmbedding (collarExtendedPositivePart d) := by
  exact (collarExternalInteriorMap_isOpenEmbedding hA).comp
    (collarLocalPositiveMap_isOpenEmbedding hA d)

theorem collarExtendedChart_positive
    {X : Type*} [TopologicalSpace X] {A : Set X} (d : collarLocalData X A)
    (z : d.carrier × Set.Ioo (0 : ℝ) 1) :
    collarExtendedChart d
      (z.1, ⟨z.2.val, (le_trans (by norm_num) z.2.property.1.le), z.2.property.2⟩) =
      collarExtendedPositivePart d z := by
  apply Subtype.ext
  rw [collarExtendedChart_val_of_pos]
  · rfl
  · exact z.2.property.1

theorem collarExtendedChart_comp_positive
    {X : Type*} [TopologicalSpace X] {A : Set X} (d : collarLocalData X A) :
    collarExtendedChart d ∘ collarExtendedPositiveInclusion d =
      collarExtendedPositivePart d := by
  funext z
  exact collarExtendedChart_positive d z

theorem collarExtendedChart_image_mem_nhds_of_neg
    {X : Type*} [TopologicalSpace X] {A : Set X} (d : collarLocalData X A)
    {S : Set (d.carrier × Set.Ico (-2 : ℝ) 1)} (hS : IsOpen S)
    {z : d.carrier × Set.Ico (-2 : ℝ) 1} (hzS : z ∈ S) (hz : z.2.val < 0) :
    collarExtendedChart d '' S ∈ 𝓝 (collarExtendedChart d z) := by
  let q : d.carrier × Set.Ico (-2 : ℝ) 0 :=
    (z.1, ⟨z.2.val, z.2.property.1, hz⟩)
  have hq : collarExtendedNegativeInclusion d q = z := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      rfl
  let T := collarExtendedNegativeInclusion d ⁻¹' S
  have hT : IsOpen T := hS.preimage (collarExtendedNegativeInclusion_isOpenEmbedding d).continuous
  have hqT : q ∈ T := by
    change collarExtendedNegativeInclusion d q ∈ S
    rwa [hq]
  have hopen : IsOpen (collarExtendedNegativePart d '' T) :=
    (collarExtendedNegativePart_isOpenEmbedding d).isOpenMap T hT
  have hnhds : collarExtendedNegativePart d '' T ∈ 𝓝 (collarExtendedNegativePart d q) :=
    hopen.mem_nhds ⟨q, hqT, rfl⟩
  have hpoint : collarExtendedNegativePart d q = collarExtendedChart d z :=
    (congrFun (collarExtendedChart_comp_negative d) q).symm.trans
      (congrArg (collarExtendedChart d) hq)
  rw [hpoint] at hnhds
  apply mem_of_superset hnhds
  rintro y ⟨w, hw, rfl⟩
  exact ⟨collarExtendedNegativeInclusion d w, hw,
    congrFun (collarExtendedChart_comp_negative d) w⟩

theorem collarExtendedChart_image_mem_nhds_of_pos
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A)
    (d : collarLocalData X A) {S : Set (d.carrier × Set.Ico (-2 : ℝ) 1)}
    (hS : IsOpen S) {z : d.carrier × Set.Ico (-2 : ℝ) 1} (hzS : z ∈ S)
    (hz : 0 < z.2.val) : collarExtendedChart d '' S ∈ 𝓝 (collarExtendedChart d z) := by
  let q : d.carrier × Set.Ioo (0 : ℝ) 1 :=
    (z.1, ⟨z.2.val, hz, z.2.property.2⟩)
  have hq : collarExtendedPositiveInclusion d q = z := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      rfl
  let T := collarExtendedPositiveInclusion d ⁻¹' S
  have hT : IsOpen T := hS.preimage (collarExtendedPositiveInclusion_isOpenEmbedding d).continuous
  have hqT : q ∈ T := by
    change collarExtendedPositiveInclusion d q ∈ S
    rwa [hq]
  have hopen : IsOpen (collarExtendedPositivePart d '' T) :=
    (collarExtendedPositivePart_isOpenEmbedding hA d).isOpenMap T hT
  have hnhds : collarExtendedPositivePart d '' T ∈ 𝓝 (collarExtendedPositivePart d q) :=
    hopen.mem_nhds ⟨q, hqT, rfl⟩
  have hpoint : collarExtendedPositivePart d q = collarExtendedChart d z :=
    (congrFun (collarExtendedChart_comp_positive d) q).symm.trans
      (congrArg (collarExtendedChart d) hq)
  rw [hpoint] at hnhds
  apply mem_of_superset hnhds
  rintro y ⟨w, hw, rfl⟩
  exact ⟨collarExtendedPositiveInclusion d w, hw,
    congrFun (collarExtendedChart_comp_positive d) w⟩

theorem collarExtendedChart_image_mem_nhds_of_zero
    {X : Type*} [TopologicalSpace X] {A : Set X} (d : collarLocalData X A)
    {S : Set (d.carrier × Set.Ico (-2 : ℝ) 1)} (hS : IsOpen S)
    {z : d.carrier × Set.Ico (-2 : ℝ) 1} (hzS : z ∈ S) (hz : z.2.val = 0) :
    collarExtendedChart d '' S ∈ 𝓝 (collarExtendedChart d z) := by
  obtain ⟨U, V, hU, hV, hzU, hzV, hUV⟩ := (isOpen_prod_iff.mp hS) z.1 z.2 hzS
  obtain ⟨ε, hε, hεV⟩ := (Metric.isOpen_iff.mp hV) z.2 hzV
  let P : Set (d.carrier × Set.Ico (0 : ℝ) 1) := U ×ˢ {t | t.val < ε}
  have hP : IsOpen P := hU.prod (isOpen_lt continuous_subtype_val continuous_const)
  let W : Set X := d.map '' P
  have hW : IsOpen W := d.isOpenEmbedding_map.isOpenMap P hP
  let N : Set (collarExternal X A) :=
    (Subtype.val : collarExternal X A → X × ℝ) ⁻¹' (W ×ˢ Set.Ioi (-ε))
  have hN : IsOpen N := (hW.prod isOpen_Ioi).preimage continuous_subtype_val
  have hzW : z.1.val.val ∈ W := by
    refine ⟨(z.1, ⟨0, by simp⟩), ⟨hzU, hε⟩, ?_⟩
    exact d.map_zero z.1
  have hzN : collarExtendedChart d z ∈ N := by
    change (collarExtendedChart d z).val.1 ∈ W ∧ -ε < (collarExtendedChart d z).val.2
    rw [collarExtendedChart_val_of_nonpos d z hz.le]
    exact ⟨hzW, by simpa [hz] using hε⟩
  apply mem_of_superset (hN.mem_nhds hzN)
  intro y hyN
  change y.val.1 ∈ W ∧ -ε < y.val.2 at hyN
  rcases hyN.1 with ⟨p, hpP, hpy⟩
  rcases hpP with ⟨hpU, hpε⟩
  rcases y.property with hy0 | hyA
  · let t : Set.Ico (-2 : ℝ) 1 :=
      ⟨p.2.val, le_trans (by norm_num) p.2.property.1, p.2.property.2⟩
    have htV : t ∈ V := by
      apply hεV
      rw [Metric.mem_ball, Subtype.dist_eq]
      simpa [t, hz, abs_of_nonneg p.2.property.1] using hpε
    let w : d.carrier × Set.Ico (-2 : ℝ) 1 := (p.1, t)
    refine ⟨w, hUV ⟨hpU, htV⟩, ?_⟩
    apply Subtype.ext
    rw [collarExtendedChart_val_of_nonneg d w p.2.property.1]
    have ht : (⟨t.val, p.2.property.1, t.property.2⟩ : Set.Ico (0 : ℝ) 1) = p.2 := by
      apply Subtype.ext
      rfl
    rw [ht]
    apply Prod.ext
    · exact hpy
    · exact hy0.2.symm
  · have hp0 : p.2.val = 0 := by
      apply le_antisymm
      · by_contra hp
        have hp' : 0 < p.2.val := lt_of_not_ge hp
        apply d.map_not_mem p hp'
        exact (congrArg (fun x : X ↦ x ∈ A) hpy).mpr hyA.1
      · exact p.2.property.1
    have hpx : p.1.val.val = y.val.1 := by
      have hpcoord : p.2 = ⟨0, by simp⟩ := by
        apply Subtype.ext
        exact hp0
      calc
        p.1.val.val = d.map (p.1, ⟨0, by simp⟩) := (d.map_zero p.1).symm
        _ = d.map p := by rw [← hpcoord]
        _ = y.val.1 := hpy
    let t : Set.Ico (-2 : ℝ) 1 :=
      ⟨y.val.2, hyA.2.1, hyA.2.2.trans_lt (by norm_num)⟩
    have htV : t ∈ V := by
      apply hεV
      rw [Metric.mem_ball, Subtype.dist_eq]
      have ht0 : t.val ≤ 0 := by
        exact hyA.2.2
      have hdist : dist t.val z.2.val = -t.val := by
        simp [hz, abs_of_nonpos ht0]
      rw [hdist]
      change -y.val.2 < ε
      linarith
    let w : d.carrier × Set.Ico (-2 : ℝ) 1 := (p.1, t)
    refine ⟨w, hUV ⟨hpU, htV⟩, ?_⟩
    apply Subtype.ext
    rw [collarExtendedChart_val_of_nonpos d w hyA.2.2]
    exact Prod.ext hpx rfl

theorem collarExtendedChart_isOpenMap
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A)
    (d : collarLocalData X A) : IsOpenMap (collarExtendedChart d) := by
  intro S hS
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨z, hzS, rfl⟩
  rcases lt_trichotomy z.2.val 0 with hz | hz | hz
  · exact collarExtendedChart_image_mem_nhds_of_neg d hS hzS hz
  · exact collarExtendedChart_image_mem_nhds_of_zero d hS hzS hz
  · exact collarExtendedChart_image_mem_nhds_of_pos hA d hS hzS hz

theorem collarExtendedChart_isOpenEmbedding
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A)
    (d : collarLocalData X A) : Topology.IsOpenEmbedding (collarExtendedChart d) := by
  exact Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    (collarExtendedChart_continuous d) (collarExtendedChart_injective d)
    (collarExtendedChart_isOpenMap hA d)

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
