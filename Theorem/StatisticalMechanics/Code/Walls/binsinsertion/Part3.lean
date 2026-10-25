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
import Def.StatisticalMechanics.Code.Walls.binsinsertion.Part2
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


theorem bins_ShellExtEvent_dependsOn (n : ℕ) (v₁ v₂ v₃ u₁ u₂ u₃ : Site 2) :
    DependsOn (bins_ShellExtEvent n v₁ v₂ v₃ u₁ u₂ u₃)
      ((↑(bondFinsetTouch 2 n) : Set (Sym2 (Site 2)))ᶜ) := by
  intro ω ω' hag
  simp only [bins_ShellExtEvent, Set.mem_setOf_eq]
  have hExt := (bins_ExtEvent_dependsOn (bondFinsetTouch 2 n) u₁ u₂ u₃) ω ω' hag
  tauto

theorem bins_ShellExtEvent_measurable (n : ℕ) (v₁ v₂ v₃ u₁ u₂ u₃ : Site 2) :
    MeasurableSet (bins_ShellExtEvent n v₁ v₂ v₃ u₁ u₂ u₃) := by
  by_cases h : (v₁ ∈ box 2 n ∧ (hypercubicLattice 2).Adj v₁ u₁) ∧
      (v₂ ∈ box 2 n ∧ (hypercubicLattice 2).Adj v₂ u₂) ∧
      (v₃ ∈ box 2 n ∧ (hypercubicLattice 2).Adj v₃ u₃)
  · have heq : bins_ShellExtEvent n v₁ v₂ v₃ u₁ u₂ u₃ =
        bins_ExtEvent (bondFinsetTouch 2 n) u₁ u₂ u₃ := by
      ext ω
      simp only [bins_ShellExtEvent, Set.mem_setOf_eq]
      constructor
      · exact fun h' ↦ h'.2.2.2
      · intro h'
        exact ⟨h.1, h.2.1, h.2.2, h'⟩
    rw [heq]
    exact bins_ExtEvent_measurable _ _ _ _
  · have heq : bins_ShellExtEvent n v₁ v₂ v₃ u₁ u₂ u₃ = ∅ := by
      ext ω
      simp only [bins_ShellExtEvent, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      tauto
    rw [heq]
    exact MeasurableSet.empty


theorem bins_threeMeetBox_subset_iUnion_ShellExtEvent (n : ℕ) :
    threeMeetBox 2 n ⊆
      ⋃ v₁ : Site 2, ⋃ v₂ : Site 2, ⋃ v₃ : Site 2,
      ⋃ u₁ : Site 2, ⋃ u₂ : Site 2, ⋃ u₃ : Site 2,
        bins_ShellExtEvent n v₁ v₂ v₃ u₁ u₂ u₃ := by
  intro ω hω
  obtain ⟨_, x₁, x₂, x₃, hx1, hx2, hx3, hi1, hi2, hi3, hd12, hd13, hd23⟩ := hω
  have inAround {x : Site 2} (hx : x ∈ box 2 n) : x ∈ bc61_boxAround 2 n 0 := by
    rw [bc61_boxAround_zero, show boxFinsetBK 2 n = boxFinset 2 n by rfl, mem_boxFinset]
    exact hx
  obtain ⟨u₁, ⟨v₁, hv1, ha1⟩, hu1, hc1⟩ :=
    bc117_attach_of_meetsBox hi1 (inAround hx1) rfl
  obtain ⟨u₂, ⟨v₂, hv2, ha2⟩, hu2, hc2⟩ :=
    bc117_attach_of_meetsBox hi2 (inAround hx2) rfl
  obtain ⟨u₃, ⟨v₃, hv3, ha3⟩, hu3, hc3⟩ :=
    bc117_attach_of_meetsBox hi3 (inAround hx3) rfl
  have hv1' : v₁ ∈ box 2 n := by
    rwa [bc61_boxAround_zero, show boxFinsetBK 2 n = boxFinset 2 n by rfl, mem_boxFinset] at hv1
  have hv2' : v₂ ∈ box 2 n := by
    rwa [bc61_boxAround_zero, show boxFinsetBK 2 n = boxFinset 2 n by rfl, mem_boxFinset] at hv2
  have hv3' : v₃ ∈ box 2 n := by
    rwa [bc61_boxAround_zero, show boxFinsetBK 2 n = boxFinset 2 n by rfl, mem_boxFinset] at hv3
  have hu1' : (cluster 2 (removeSites (boxFinset 2 n) ω) u₁).Infinite := by
    rwa [bc61_boxAround_zero, show boxFinsetBK 2 n = boxFinset 2 n by rfl] at hu1
  have hu2' : (cluster 2 (removeSites (boxFinset 2 n) ω) u₂).Infinite := by
    rwa [bc61_boxAround_zero, show boxFinsetBK 2 n = boxFinset 2 n by rfl] at hu2
  have hu3' : (cluster 2 (removeSites (boxFinset 2 n) ω) u₃).Infinite := by
    rwa [bc61_boxAround_zero, show boxFinsetBK 2 n = boxFinset 2 n by rfl] at hu3
  have hcut12 : cluster 2 (removeSites (boxFinset 2 n) ω) u₁ ≠
      cluster 2 (removeSites (boxFinset 2 n) ω) u₂ := by
    intro h
    have hc : Connected 2 (removeSites (boxFinset 2 n) ω) u₁ u₂ := mem_cluster.mp (by
      rw [h]; exact self_mem_cluster _ u₂)
    have hc' := connected_mono (daep_removeSites_le (boxFinset 2 n) ω) hc
    exact hd12 (by rw [hc1, hc2]; exact cluster_eq_of_connected hc')
  have hcut13 : cluster 2 (removeSites (boxFinset 2 n) ω) u₁ ≠
      cluster 2 (removeSites (boxFinset 2 n) ω) u₃ := by
    intro h
    have hc : Connected 2 (removeSites (boxFinset 2 n) ω) u₁ u₃ := mem_cluster.mp (by
      rw [h]; exact self_mem_cluster _ u₃)
    have hc' := connected_mono (daep_removeSites_le (boxFinset 2 n) ω) hc
    exact hd13 (by rw [hc1, hc3]; exact cluster_eq_of_connected hc')
  have hcut23 : cluster 2 (removeSites (boxFinset 2 n) ω) u₂ ≠
      cluster 2 (removeSites (boxFinset 2 n) ω) u₃ := by
    intro h
    have hc : Connected 2 (removeSites (boxFinset 2 n) ω) u₂ u₃ := mem_cluster.mp (by
      rw [h]; exact self_mem_cluster _ u₃)
    have hc' := connected_mono (daep_removeSites_le (boxFinset 2 n) ω) hc
    exact hd23 (by rw [hc2, hc3]; exact cluster_eq_of_connected hc')
  refine Set.mem_iUnion.mpr ⟨v₁, Set.mem_iUnion.mpr ⟨v₂, Set.mem_iUnion.mpr ⟨v₃,
    Set.mem_iUnion.mpr ⟨u₁, Set.mem_iUnion.mpr ⟨u₂, Set.mem_iUnion.mpr ⟨u₃, ?_⟩⟩⟩⟩⟩⟩
  refine ⟨⟨hv1', ha1.1⟩, ⟨hv2', ha2.1⟩, ⟨hv3', ha3.1⟩, ?_⟩
  change bins_ExtPred u₁ u₂ u₃
    (removeSite 0 (bpt2_closeI (bondFinsetTouch 2 n) ω))
  unfold bins_ExtPred
  rw [bins_cluster_closeTouch_eq_removeBox,
    bins_cluster_closeTouch_eq_removeBox, bins_cluster_closeTouch_eq_removeBox]
  exact ⟨⟨hu1', hu2', hu3'⟩, hcut12, hcut13, hcut23⟩


theorem bins_exists_ShellExtEvent_pos (p : ℝ≥0) (hp1 : p ≤ 1) (n : ℕ)
    (hpos : 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (threeMeetBox 2 n)) :
    ∃ v₁ v₂ v₃ u₁ u₂ u₃ : Site 2,
      0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
        (bins_ShellExtEvent n v₁ v₂ v₃ u₁ u₂ u₃) := by
  let μ := bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
  by_contra hcon
  simp only [not_exists, not_lt, nonpos_iff_eq_zero] at hcon
  have hu : μ (⋃ v₁ : Site 2, ⋃ v₂ : Site 2, ⋃ v₃ : Site 2,
      ⋃ u₁ : Site 2, ⋃ u₂ : Site 2, ⋃ u₃ : Site 2,
      bins_ShellExtEvent n v₁ v₂ v₃ u₁ u₂ u₃) = 0 := by
    refine measure_iUnion_null fun v₁ ↦ measure_iUnion_null fun v₂ ↦
      measure_iUnion_null fun v₃ ↦ measure_iUnion_null fun u₁ ↦
      measure_iUnion_null fun u₂ ↦ measure_iUnion_null fun u₃ ↦ ?_
    exact hcon v₁ v₂ v₃ u₁ u₂ u₃
  have hz : μ (threeMeetBox 2 n) = 0 := le_antisymm
    ((measure_mono (bins_threeMeetBox_subset_iUnion_ShellExtEvent n)).trans_eq hu) bot_le
  apply (ne_of_gt hpos)
  simpa [μ] using hz


end StatMech.Walls
