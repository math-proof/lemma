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
import Def.StatisticalMechanics.Code.Walls.binsinsertion.Part5
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


theorem bins_outside_neighbor_side {n : ℕ} {v u : Site 2}
    (hv : v ∈ box 2 n) (hadj : (hypercubicLattice 2).Adj v u) (hu : u ∉ box 2 n) :
    u 0 = (n : ℤ) + 1 ∨ u 0 = -((n : ℤ) + 1) ∨
      u 1 = (n : ℤ) + 1 ∨ u 1 = -((n : ℤ) + 1) := by
  rw [mem_box] at hv hu
  simp only [not_forall, not_le] at hu
  obtain ⟨q, hq⟩ := hu
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
  have hv0 := hv 0
  have hv1 := hv 1
  fin_cases q
  · change n < (u 0).natAbs at hq
    by_cases hsign : 0 ≤ u 0
    · have hq' : (n : ℤ) < (u 0).natAbs := by exact_mod_cast hq
      rw [Int.natAbs_of_nonneg hsign] at hq'
      left
      omega
    · have hq' : (n : ℤ) < (u 0).natAbs := by exact_mod_cast hq
      rw [Int.ofNat_natAbs_of_nonpos (by omega)] at hq'
      right; left
      omega
  · change n < (u 1).natAbs at hq
    by_cases hsign : 0 ≤ u 1
    · have hq' : (n : ℤ) < (u 1).natAbs := by exact_mod_cast hq
      rw [Int.natAbs_of_nonneg hsign] at hq'
      right; right; left
      omega
    · have hq' : (n : ℤ) < (u 1).natAbs := by exact_mod_cast hq
      rw [Int.ofNat_natAbs_of_nonpos (by omega)] at hq'
      right; right; right
      omega


theorem bins_v_coord_of_outSide {n : ℕ} {v u : Site 2}
    (hv : v ∈ box 2 n) (hadj : (hypercubicLattice 2).Adj v u) (hu : u ∉ box 2 n) :
    (bins_outSide n u = 0 → v 0 = (n : ℤ)) ∧
    (bins_outSide n u = 1 → v 0 = -(n : ℤ)) ∧
    (bins_outSide n u = 2 → v 1 = (n : ℤ)) ∧
    (bins_outSide n u = 3 → v 1 = -(n : ℤ)) := by
  have hs := bins_outside_neighbor_side hv hadj hu
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
  unfold bins_outSide
  split_ifs with hR hL hT <;> simp_all <;> omega


theorem bins_u_coord_of_outSide {n : ℕ} {v u : Site 2}
    (hv : v ∈ box 2 n) (hadj : (hypercubicLattice 2).Adj v u) (hu : u ∉ box 2 n) :
    (bins_outSide n u = 0 → u 0 = (n : ℤ) + 1 ∧ u 1 = v 1) ∧
    (bins_outSide n u = 1 → u 0 = -((n : ℤ) + 1) ∧ u 1 = v 1) ∧
    (bins_outSide n u = 2 → u 0 = v 0 ∧ u 1 = (n : ℤ) + 1) ∧
    (bins_outSide n u = 3 → u 0 = v 0 ∧ u 1 = -((n : ℤ) + 1)) := by
  have hs := bins_outside_neighbor_side hv hadj hu
  have hc := bins_v_coord_of_outSide hv hadj hu
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
  unfold bins_outSide at hc ⊢
  split_ifs with hR hL hT <;> simp_all <;> omega


theorem bins_NineShellEvent_three_same_side {n : ℕ} {v u : Fin 9 → Site 2}
    {ω : ConfigSpace (Sym2 (Site 2))} (hE : ω ∈ bins_NineShellEvent n v u) :
    ∃ i j k : Fin 9, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      v i ≠ v j ∧ v i ≠ v k ∧ v j ≠ v k ∧
      ((v i 0 = (n : ℤ) ∧ v j 0 = (n : ℤ) ∧ v k 0 = (n : ℤ)) ∨
       (v i 0 = -(n : ℤ) ∧ v j 0 = -(n : ℤ) ∧ v k 0 = -(n : ℤ)) ∨
       (v i 1 = (n : ℤ) ∧ v j 1 = (n : ℤ) ∧ v k 1 = (n : ℤ)) ∨
       (v i 1 = -(n : ℤ) ∧ v j 1 = -(n : ℤ) ∧ v k 1 = -(n : ℤ))) := by
  obtain ⟨hgeom, hinf, hdist⟩ := hE
  have huout (i : Fin 9) : u i ∉ box 2 n := by
    have hi : (cluster 2 (removeSites (boxFinset 2 n) ω) (u i)).Infinite := by
      rw [← bins_cluster_closeTouch_eq_removeBox]
      exact hinf i
    exact fun h ↦ stac_infiniteCluster_notMem (boxFinset 2 n) ω hi (mem_boxFinset.mpr h)
  let side : Fin 9 → Fin 4 := fun i ↦ bins_outSide n (u i)
  obtain ⟨s, hs⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card (f := side) (n := 2) (by decide)
  let F := Finset.univ.filter (fun i ↦ side i = s)
  have hF : 2 < F.card := by simpa [F] using hs
  obtain ⟨t, ht, htcard⟩ := Finset.exists_subset_card_eq (show 3 ≤ F.card by omega)
  obtain ⟨i, j, k, hij, hik, hjk, rfl⟩ := Finset.card_eq_three.mp htcard
  have hiF : i ∈ F := ht (by simp)
  have hjF : j ∈ F := ht (by simp)
  have hkF : k ∈ F := ht (by simp)
  have hi : side i = s := by simpa [F] using hiF
  have hj : side j = s := by simpa [F] using hjF
  have hk : side k = s := by simpa [F] using hkF
  have huij : u i ≠ u j := by
    intro h
    exact hdist i j hij (by rw [h])
  have huik : u i ≠ u k := by
    intro h
    exact hdist i k hik (by rw [h])
  have hujk : u j ≠ u k := by
    intro h
    exact hdist j k hjk (by rw [h])
  have vinj : ∀ {a b : Fin 9}, side a = side b → u a ≠ u b → v a ≠ v b := by
    intro a b hab huab hvab
    apply huab
    have ha := bins_u_coord_of_outSide (hgeom a).1 (hgeom a).2 (huout a)
    have hb := bins_u_coord_of_outSide (hgeom b).1 (hgeom b).2 (huout b)
    have hab' : bins_outSide n (u a) = bins_outSide n (u b) := by simpa [side] using hab
    generalize hsa : bins_outSide n (u a) = sa
    fin_cases sa
    · have hsb : bins_outSide n (u b) = 0 := hab'.symm.trans hsa
      have ha0 := ha.1 hsa
      have hb0 := hb.1 hsb
      ext q
      fin_cases q
      · change u a 0 = u b 0
        rw [ha0.1, hb0.1]
      · change u a 1 = u b 1
        rw [ha0.2, hb0.2, congrFun hvab 1]
    · have hsb : bins_outSide n (u b) = 1 := hab'.symm.trans hsa
      have ha1 := ha.2.1 hsa
      have hb1 := hb.2.1 hsb
      ext q
      fin_cases q
      · change u a 0 = u b 0
        rw [ha1.1, hb1.1]
      · change u a 1 = u b 1
        rw [ha1.2, hb1.2, congrFun hvab 1]
    · have hsb : bins_outSide n (u b) = 2 := hab'.symm.trans hsa
      have ha2 := ha.2.2.1 hsa
      have hb2 := hb.2.2.1 hsb
      ext q
      fin_cases q
      · change u a 0 = u b 0
        rw [ha2.1, hb2.1, congrFun hvab 0]
      · change u a 1 = u b 1
        rw [ha2.2, hb2.2]
    · have hsb : bins_outSide n (u b) = 3 := hab'.symm.trans hsa
      have ha3 := ha.2.2.2 hsa
      have hb3 := hb.2.2.2 hsb
      ext q
      fin_cases q
      · change u a 0 = u b 0
        rw [ha3.1, hb3.1, congrFun hvab 0]
      · change u a 1 = u b 1
        rw [ha3.2, hb3.2]
  have hvij : v i ≠ v j := vinj (hi.trans hj.symm) huij
  have hvik : v i ≠ v k := vinj (hi.trans hk.symm) huik
  have hvjk : v j ≠ v k := vinj (hj.trans hk.symm) hujk
  refine ⟨i, j, k, hij, hik, hjk, hvij, hvik, hvjk, ?_⟩
  have hci := bins_v_coord_of_outSide (hgeom i).1 (hgeom i).2 (huout i)
  have hcj := bins_v_coord_of_outSide (hgeom j).1 (hgeom j).2 (huout j)
  have hck := bins_v_coord_of_outSide (hgeom k).1 (hgeom k).2 (huout k)
  fin_cases s
  · left
    exact ⟨hci.1 (by simpa [side] using hi), hcj.1 (by simpa [side] using hj),
      hck.1 (by simpa [side] using hk)⟩
  · right; left
    exact ⟨hci.2.1 (by simpa [side] using hi), hcj.2.1 (by simpa [side] using hj),
      hck.2.1 (by simpa [side] using hk)⟩
  · right; right; left
    exact ⟨hci.2.2.1 (by simpa [side] using hi),
      hcj.2.2.1 (by simpa [side] using hj), hck.2.2.1 (by simpa [side] using hk)⟩
  · right; right; right
    exact ⟨hci.2.2.2 (by simpa [side] using hi),
      hcj.2.2.2 (by simpa [side] using hj), hck.2.2.2 (by simpa [side] using hk)⟩


theorem bins_routePackage_of_corridors (p : ℝ≥0) (hp1 : p ≤ 1) (m : ℕ)
    (u₁ u₂ u₃ : Site 2) (I : Finset (Sym2 (Site 2)))
    (hu₁ : u₁ ≠ ![0, 0]) (hu₂ : u₂ ≠ ![0, 0]) (hu₃ : u₃ ≠ ![0, 0])
    (hC : bcor_Corridors m u₁ u₂ u₃)
    (hXpos : 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
      (bins_ExtEvent I u₁ u₂ u₃))
    (hpattern : ∀ a₁ a₂ a₃ : Site 2,
      ((hypercubicLattice 2).Adj 0 a₁ ∧ (hypercubicLattice 2).Adj 0 a₂ ∧
        (hypercubicLattice 2).Adj 0 a₃) →
      (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) →
      ∃ η₀ : ConfigSpace ↥I,
        cylinder I ({η₀} : Set (ConfigSpace ↥I)) ∩ bins_ExtEvent I u₁ u₂ u₃
          ⊆ NeighborTrifPrecursor 2 a₁ a₂ a₃) :
    ∃ (η₀ : ConfigSpace ↥I) (a₁ a₂ a₃ : Site 2)
      (X : Set (ConfigSpace (Sym2 (Site 2)))),
      (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
      ((hypercubicLattice 2).Adj 0 a₁ ∧ (hypercubicLattice 2).Adj 0 a₂ ∧
        (hypercubicLattice 2).Adj 0 a₃) ∧
      MeasurableSet X ∧ DependsOn X ((↑I : Set (Sym2 (Site 2)))ᶜ) ∧
      0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 X ∧
      cylinder I ({η₀} : Set (ConfigSpace ↥I)) ∩ X
        ⊆ NeighborTrifPrecursor 2 a₁ a₂ a₃ := by
  obtain ⟨a₁, a₂, a₃, hadj, hne⟩ := bcor_firstSteps m hu₁ hu₂ hu₃ hC
  obtain ⟨η₀, hgeo⟩ := hpattern a₁ a₂ a₃ hadj hne
  exact ⟨η₀, a₁, a₂, a₃, bins_ExtEvent I u₁ u₂ u₃,
    hne, hadj, bins_ExtEvent_measurable I u₁ u₂ u₃,
    bins_ExtEvent_dependsOn I u₁ u₂ u₃, hXpos, hgeo⟩


end StatMech.Walls
