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
import Def.StatisticalMechanics.Code.Walls.binsinsertion.Part4
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


theorem bins_NineMeetBox_subset_iUnion_NineShellEvent (n : ℕ) :
    bins_NineMeetBox n ⊆
      ⋃ v : Fin 9 → Site 2, ⋃ u : Fin 9 → Site 2, bins_NineShellEvent n v u := by
  intro ω hω
  obtain ⟨_, x, hx, hdist⟩ := hω
  have inAround (i : Fin 9) : x i ∈ bc61_boxAround 2 n 0 := by
    rw [bc61_boxAround_zero, show boxFinsetBK 2 n = boxFinset 2 n by rfl, mem_boxFinset]
    exact (hx i).1
  have hatt (i : Fin 9) : ∃ a : Site 2,
      (∃ b ∈ bc61_boxAround 2 n 0, (openSubgraph 2 ω).Adj b a) ∧
      (cluster 2 (removeSites (bc61_boxAround 2 n 0) ω) a).Infinite ∧
      cluster 2 ω (x i) = cluster 2 ω a :=
    bc117_attach_of_meetsBox (hx i).2 (inAround i) rfl
  let u : Fin 9 → Site 2 := fun i ↦ Classical.choose (hatt i)
  have hu (i : Fin 9) := Classical.choose_spec (hatt i)
  let v : Fin 9 → Site 2 := fun i ↦ Classical.choose (hu i).1
  have hv (i : Fin 9) := Classical.choose_spec (hu i).1
  have hvbox (i : Fin 9) : v i ∈ box 2 n := by
    exact bc61_mem_boxAround_zero.mp (hv i).1
  have huinf (i : Fin 9) :
      (cluster 2 (removeSites (boxFinset 2 n) ω) (u i)).Infinite := by
    change (cluster 2 (removeSites (boxFinset 2 n) ω)
      (Classical.choose (hatt i))).Infinite
    have hT : bc61_boxAround 2 n 0 = boxFinset 2 n := by
      rw [bc61_boxAround_zero]
      rfl
    simpa only [hT] using (hu i).2.1
  have hcut (i j : Fin 9) (hij : i ≠ j) :
      cluster 2 (removeSites (boxFinset 2 n) ω) (u i) ≠
      cluster 2 (removeSites (boxFinset 2 n) ω) (u j) := by
    intro h
    have hc : Connected 2 (removeSites (boxFinset 2 n) ω) (u i) (u j) := mem_cluster.mp (by
      rw [h]
      exact self_mem_cluster _ (u j))
    have hc' : Connected 2 ω (u i) (u j) :=
      connected_mono (daep_removeSites_le (boxFinset 2 n) ω) hc
    apply hdist i j hij
    rw [(hu i).2.2, (hu j).2.2]
    exact cluster_eq_of_connected hc'
  refine Set.mem_iUnion.mpr ⟨v, Set.mem_iUnion.mpr ⟨u, ?_⟩⟩
  refine ⟨fun i ↦ ⟨hvbox i, (hv i).2.1⟩, ?_, ?_⟩
  · intro i
    rw [bins_cluster_closeTouch_eq_removeBox]
    exact huinf i
  · intro i j hij
    rw [bins_cluster_closeTouch_eq_removeBox, bins_cluster_closeTouch_eq_removeBox]
    exact hcut i j hij


theorem bins_exists_NineShellEvent_pos (p : ℝ≥0) (hp1 : p ≤ 1) (n : ℕ)
    (hpos : 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
      (bins_NineMeetBox n)) :
    ∃ (v u : Fin 9 → Site 2),
      0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
        (bins_NineShellEvent n v u) := by
  let μ := bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
  by_contra hcon
  simp only [not_exists, not_lt, nonpos_iff_eq_zero] at hcon
  have hu : μ (⋃ v : Fin 9 → Site 2, ⋃ u : Fin 9 → Site 2,
      bins_NineShellEvent n v u) = 0 := by
    refine measure_iUnion_null fun v ↦ measure_iUnion_null fun u ↦ hcon v u
  have hz : μ (bins_NineMeetBox n) = 0 := le_antisymm
    ((measure_mono (bins_NineMeetBox_subset_iUnion_NineShellEvent n)).trans_eq hu) bot_le
  apply (ne_of_gt hpos)
  simpa [μ] using hz


theorem bins_exists_NineShellEvent_pos_of_threeMeetBox
    (p : ℝ≥0) (hp1 : p ≤ 1) (n : ℕ)
    (hpos : 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
      (threeMeetBox 2 n)) :
    ∃ (m : ℕ) (v u : Fin 9 → Site 2),
      0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
        (bins_NineShellEvent m v u) := by
  have htop : 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
      {ω : ConfigSpace (Sym2 (Site 2)) | numInfiniteClusters 2 ω = ⊤} :=
    lt_of_lt_of_le hpos (measure_mono (fun _ h ↦ h.1))
  obtain ⟨m, hm⟩ := bins_exists_NineMeetBox_pos p hp1 htop
  obtain ⟨v, u, hvu⟩ := bins_exists_NineShellEvent_pos p hp1 m hm
  exact ⟨m, v, u, hvu⟩


end StatMech.Walls
