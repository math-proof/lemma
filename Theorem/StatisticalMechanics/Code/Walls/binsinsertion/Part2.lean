/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/binsinsertion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bcl2close.Part2
import Theorem.StatisticalMechanics.Code.Walls.bcorcorridors.Part5
import Theorem.StatisticalMechanics.Code.Walls.bc117mergeproof.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.HisingBoxClose.Part3
import Def.StatisticalMechanics.Code.Walls.binsinsertion
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation
open StatMech.Ising StatMech.IsingFK


namespace StatMech.Walls

set_option linter.style.longLine false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option maxRecDepth 4000


theorem bins_ExtEvent_dependsOn (I : Finset (Sym2 (Site 2))) (u₁ u₂ u₃ : Site 2) :
    DependsOn (bins_ExtEvent I u₁ u₂ u₃) ((↑I : Set (Sym2 (Site 2)))ᶜ) := by
  intro ω ω' hag
  change bins_ExtPred u₁ u₂ u₃ (removeSite 0 (bpt2_closeI I ω))
      ↔ bins_ExtPred u₁ u₂ u₃ (removeSite 0 (bpt2_closeI I ω'))
  rw [bpt2_removeSite_closeI_congr I hag]


theorem bins_measurable_closeI (I : Finset (Sym2 (Site 2))) :
    Measurable (fun ω : ConfigSpace (Sym2 (Site 2)) ↦ bpt2_closeI I ω) := by
  apply measurable_pi_lambda
  intro e
  unfold bpt2_closeI
  by_cases he : e ∈ I
  · simp [he]
  · simp only [he, if_false]
    exact measurable_pi_apply e


theorem bins_ExtEvent_measurable (I : Finset (Sym2 (Site 2))) (u₁ u₂ u₃ : Site 2) :
    MeasurableSet (bins_ExtEvent I u₁ u₂ u₃) := by
  let f : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2)) :=
    fun ω ↦ removeSite 0 (bpt2_closeI I ω)
  have hf : Measurable f := (measurable_removeSite 0).comp (bins_measurable_closeI I)
  have hinf : ∀ u : Site 2, MeasurableSet {ω | (cluster 2 (f ω) u).Infinite} := by
    intro u
    exact hf (measurableSet_clusterInfinite u)
  have hconn : ∀ u v : Site 2, MeasurableSet {ω | Connected 2 (f ω) u v} := by
    intro u v
    exact hf (measurableSet_connected u v)
  have heq : bins_ExtEvent I u₁ u₂ u₃ =
      (({ω | (cluster 2 (f ω) u₁).Infinite} ∩
        {ω | (cluster 2 (f ω) u₂).Infinite}) ∩
        {ω | (cluster 2 (f ω) u₃).Infinite}) ∩
      ((({ω | Connected 2 (f ω) u₁ u₂}ᶜ) ∩
        ({ω | Connected 2 (f ω) u₁ u₃}ᶜ)) ∩
        ({ω | Connected 2 (f ω) u₂ u₃}ᶜ)) := by
    ext ω
    simp only [bins_ExtEvent, bins_ExtPred, Set.mem_setOf_eq, Set.mem_inter_iff,
      Set.mem_compl_iff, f]
    constructor
    · rintro ⟨⟨hi1, hi2, hi3⟩, hd12, hd13, hd23⟩
      exact ⟨⟨⟨hi1, hi2⟩, hi3⟩,
        ⟨⟨fun hc ↦ hd12 (cluster_eq_of_connected hc),
          fun hc ↦ hd13 (cluster_eq_of_connected hc)⟩,
          fun hc ↦ hd23 (cluster_eq_of_connected hc)⟩⟩
    · rintro ⟨⟨⟨hi1, hi2⟩, hi3⟩, ⟨⟨hd12, hd13⟩, hd23⟩⟩
      exact ⟨⟨hi1, hi2, hi3⟩,
        fun h ↦ hd12 (mem_cluster.mp (by rw [h]; exact self_mem_cluster _ u₂)),
        fun h ↦ hd13 (mem_cluster.mp (by rw [h]; exact self_mem_cluster _ u₃)),
        fun h ↦ hd23 (mem_cluster.mp (by rw [h]; exact self_mem_cluster _ u₃))⟩
  rw [heq]
  exact (((hinf u₁).inter (hinf u₂)).inter (hinf u₃)).inter
    ((((hconn u₁ u₂).compl).inter ((hconn u₁ u₃).compl)).inter
      ((hconn u₂ u₃).compl))


theorem bins_exists_ExtEvent_pos_of_cover (p : NNReal) (hp1 : p ≤ 1) (n : ℕ)
    (I : Finset (Sym2 (Site 2)))
    (hpos : 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (threeMeetBox 2 n))
    (hcover : threeMeetBox 2 n ⊆
      ⋃ u₁ : Site 2, ⋃ u₂ : Site 2, ⋃ u₃ : Site 2, bins_ExtEvent I u₁ u₂ u₃) :
    ∃ u₁ u₂ u₃ : Site 2,
      0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
        (bins_ExtEvent I u₁ u₂ u₃) := by
  let μ := bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
  by_contra hcon
  simp only [not_exists, not_lt, nonpos_iff_eq_zero] at hcon
  have hu : μ (⋃ u₁ : Site 2, ⋃ u₂ : Site 2, ⋃ u₃ : Site 2,
      bins_ExtEvent I u₁ u₂ u₃) = 0 := by
    refine measure_iUnion_null fun u₁ ↦ measure_iUnion_null fun u₂ ↦
      measure_iUnion_null fun u₃ ↦ ?_
    exact hcon u₁ u₂ u₃
  have hz : μ (threeMeetBox 2 n) = 0 :=
    le_antisymm ((measure_mono hcover).trans_eq hu) bot_le
  apply (ne_of_gt hpos)
  simpa [μ] using hz


theorem bins_openSubgraph_closeTouch_eq_removeBox (n : ℕ)
    (ω : ConfigSpace (Sym2 (Site 2))) :
    openSubgraph 2 (removeSite 0 (bpt2_closeI (bondFinsetTouch 2 n) ω)) =
      openSubgraph 2 (removeSites (boxFinset 2 n) ω) := by
  ext x y
  simp only [openSubgraph_adj]
  constructor
  · rintro ⟨hadj, hopen⟩
    refine ⟨hadj, ?_⟩
    unfold removeSite bpt2_closeI at hopen
    unfold removeSites
    have htouch : s(x,y) ∈ bondFinsetTouch 2 n ↔ x ∈ box 2 n ∨ y ∈ box 2 n := by
      rw [hbx_mem_bondFinsetTouch_iff]
      simp only [hadj, true_and]
    have hsite : (∃ t ∈ boxFinset 2 n, t ∈ s(x,y)) ↔ x ∈ box 2 n ∨ y ∈ box 2 n := by
      simp only [Sym2.mem_iff, mem_boxFinset]
      aesop
    by_cases h0 : (0 : Site 2) ∈ s(x,y)
    · simp [h0] at hopen
    · simp only [h0, if_false] at hopen
      by_cases ht : x ∈ box 2 n ∨ y ∈ box 2 n
      · rw [if_pos (htouch.mpr ht)] at hopen
        contradiction
      · rw [if_neg (fun h ↦ ht (hsite.mp h))]
        rw [if_neg (fun h ↦ ht (htouch.mp h))] at hopen
        exact hopen
  · rintro ⟨hadj, hopen⟩
    refine ⟨hadj, ?_⟩
    unfold removeSites at hopen
    unfold removeSite bpt2_closeI
    have htouch : s(x,y) ∈ bondFinsetTouch 2 n ↔ x ∈ box 2 n ∨ y ∈ box 2 n := by
      rw [hbx_mem_bondFinsetTouch_iff]
      simp only [hadj, true_and]
    have hsite : (∃ t ∈ boxFinset 2 n, t ∈ s(x,y)) ↔ x ∈ box 2 n ∨ y ∈ box 2 n := by
      simp only [Sym2.mem_iff, mem_boxFinset]
      aesop
    by_cases ht : x ∈ box 2 n ∨ y ∈ box 2 n
    · rw [if_pos (hsite.mpr ht)] at hopen
      contradiction
    · have h0 : (0 : Site 2) ∉ s(x,y) := by
        intro h
        rw [Sym2.mem_iff] at h
        rcases h with h | h <;> subst_vars <;> apply ht <;> simp [mem_box]
      rw [if_neg h0, if_neg (fun h ↦ ht (htouch.mp h))]
      rw [if_neg (fun h ↦ ht (hsite.mp h))] at hopen
      exact hopen


theorem bins_cluster_closeTouch_eq_removeBox (n : ℕ)
    (ω : ConfigSpace (Sym2 (Site 2))) (u : Site 2) :
    cluster 2 (removeSite 0 (bpt2_closeI (bondFinsetTouch 2 n) ω)) u =
      cluster 2 (removeSites (boxFinset 2 n) ω) u := by
  ext z
  change (openSubgraph 2 (removeSite 0 (bpt2_closeI (bondFinsetTouch 2 n) ω))).Reachable u z ↔
    (openSubgraph 2 (removeSites (boxFinset 2 n) ω)).Reachable u z
  rw [bins_openSubgraph_closeTouch_eq_removeBox]


theorem bins_threeMeetBox_subset_iUnion_ExtEvent_touch (n : ℕ) :
    threeMeetBox 2 n ⊆
      ⋃ u₁ : Site 2, ⋃ u₂ : Site 2, ⋃ u₃ : Site 2,
        bins_ExtEvent (bondFinsetTouch 2 n) u₁ u₂ u₃ := by
  intro ω hω
  obtain ⟨_, x₁, x₂, x₃, _, _, _, hi1, hi2, hi3, hd12, hd13, hd23⟩ := hω
  let T := boxFinset 2 n
  obtain ⟨u₁, hc1, _, hu1⟩ := bc117_boxAvoiding_external_infinite ω hi1 T
  obtain ⟨u₂, hc2, _, hu2⟩ := bc117_boxAvoiding_external_infinite ω hi2 T
  obtain ⟨u₃, hc3, _, hu3⟩ := bc117_boxAvoiding_external_infinite ω hi3 T
  have hcut12 : cluster 2 (removeSites T ω) u₁ ≠ cluster 2 (removeSites T ω) u₂ := by
    intro h
    have hc : Connected 2 (removeSites T ω) u₁ u₂ := mem_cluster.mp (by
      rw [h]
      exact self_mem_cluster _ u₂)
    have hc' : Connected 2 ω u₁ u₂ := connected_mono (daep_removeSites_le T ω) hc
    exact hd12 (cluster_eq_of_connected (hc1.trans (hc'.trans hc2.symm)))
  have hcut13 : cluster 2 (removeSites T ω) u₁ ≠ cluster 2 (removeSites T ω) u₃ := by
    intro h
    have hc : Connected 2 (removeSites T ω) u₁ u₃ := mem_cluster.mp (by
      rw [h]
      exact self_mem_cluster _ u₃)
    have hc' : Connected 2 ω u₁ u₃ := connected_mono (daep_removeSites_le T ω) hc
    exact hd13 (cluster_eq_of_connected (hc1.trans (hc'.trans hc3.symm)))
  have hcut23 : cluster 2 (removeSites T ω) u₂ ≠ cluster 2 (removeSites T ω) u₃ := by
    intro h
    have hc : Connected 2 (removeSites T ω) u₂ u₃ := mem_cluster.mp (by
      rw [h]
      exact self_mem_cluster _ u₃)
    have hc' : Connected 2 ω u₂ u₃ := connected_mono (daep_removeSites_le T ω) hc
    exact hd23 (cluster_eq_of_connected (hc2.trans (hc'.trans hc3.symm)))
  refine Set.mem_iUnion.mpr ⟨u₁, Set.mem_iUnion.mpr ⟨u₂, Set.mem_iUnion.mpr ⟨u₃, ?_⟩⟩⟩
  change bins_ExtPred u₁ u₂ u₃
    (removeSite 0 (bpt2_closeI (bondFinsetTouch 2 n) ω))
  unfold bins_ExtPred
  rw [bins_cluster_closeTouch_eq_removeBox,
    bins_cluster_closeTouch_eq_removeBox, bins_cluster_closeTouch_eq_removeBox]
  simpa [T] using ⟨⟨hu1, hu2, hu3⟩, hcut12, hcut13, hcut23⟩


theorem bins_exists_ExtEvent_touch_pos (p : NNReal) (hp1 : p ≤ 1) (n : ℕ)
    (hpos : 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (threeMeetBox 2 n)) :
    ∃ u₁ u₂ u₃ : Site 2,
      0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
        (bins_ExtEvent (bondFinsetTouch 2 n) u₁ u₂ u₃) :=
  bins_exists_ExtEvent_pos_of_cover p hp1 n (bondFinsetTouch 2 n) hpos
    (bins_threeMeetBox_subset_iUnion_ExtEvent_touch n)


end StatMech.Walls
