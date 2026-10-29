/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc58wholebox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc57coarsetrif.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc54coarse
import Theorem.StatisticalMechanics.Code.Walls.bc49finiteenergy
import Theorem.StatisticalMechanics.Code.Percolation.HrouteHighDim.Part3
import Def.StatisticalMechanics.Code.Walls.bc58wholebox.Part4
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc58_disjointRouting_of_originTrifModification {n : ℕ}
    (h : bc58_OriginTrifModification d n) : hrHD_DisjointRouting d n := by
  intro ω hω
  obtain ⟨G, a₁, a₂, a₃, hne, ⟨he1, he2, he3⟩, ⟨hi1, hi2, hi3⟩, hsep⟩ := h ω hω
  exact ⟨G, a₁, a₂, a₃, hne, ⟨he1.1, he2.1, he3.1⟩, ⟨hi1, hi2, hi3⟩, hsep⟩


theorem bc58_hroute_of_originTrifModification
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ)
    (hmod : ∀ n : ℕ, bc58_OriginTrifModification d n) :
    ∀ n : ℕ, 0 < μ (threeMeetBox d n) →
      ∃ a₁ a₂ a₃ : Site d, 0 < μ (NeighborTrifPrecursor d a₁ a₂ a₃) :=
  hrHD_route_of_routing μ hfe (fun n => bc58_disjointRouting_of_originTrifModification (hmod n))


theorem bc58_burton_keane_bernoulli_of_originTrifModification (hd : 1 ≤ d)
    (p : NNReal) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hmod : ∀ n : ℕ, bc58_OriginTrifModification d n) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  bc54_burton_keane_bernoulli hd p hp1 hp0
    (bc58_hroute_of_originTrifModification (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1)
      (bkc_bernoulli_hasFiniteEnergyMerge p hp1 hp0) hmod)


theorem bc58_origin_nbr_cases {a : Site 2} (hadj : (hypercubicLattice 2).Adj 0 a) :
    a = bc58_p 1 0 ∨ a = bc58_p (-1) 0 ∨ a = bc58_p 0 1 ∨ a = bc58_p 0 (-1) := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
  simp only [Pi.zero_apply, zero_sub, Int.natAbs_neg] at hadj
  
  have key : (a 0 = 1 ∧ a 1 = 0) ∨ (a 0 = -1 ∧ a 1 = 0) ∨
      (a 0 = 0 ∧ a 1 = 1) ∨ (a 0 = 0 ∧ a 1 = -1) := by omega
  have hcoord : a = bc58_p (a 0) (a 1) := by
    funext i; fin_cases i <;> simp [bc58_p]
  rcases key with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; rw [hcoord, h1, h2]
  · right; left; rw [hcoord, h1, h2]
  · right; right; left; rw [hcoord, h1, h2]
  · right; right; right; rw [hcoord, h1, h2]


theorem bc58_origin_nbr_connected_to_e {k : ℕ} (hk : 1 ≤ k) (ω : ConfigSpace (Sym2 (Site 2)))
    {a : Site 2} (hadj : (hypercubicLattice 2).Adj 0 a) :
    Connected 2 (removeSite 0 (bc58_boxOpen 2 k ω)) a (bc58_p 1 0) := by
  have hk1 : (1 : ℤ).natAbs ≤ k := by simpa using hk
  have hkm1 : ((-1 : ℤ)).natAbs ≤ k := by simpa using hk
  have hk0 : (0 : ℤ).natAbs ≤ k := by simp
  
  have m10 : bc58_p 1 0 ∈ box 2 k := bc58_p_mem_box hk1 hk0
  have m11 : bc58_p 1 1 ∈ box 2 k := bc58_p_mem_box hk1 hk1
  have m01 : bc58_p 0 1 ∈ box 2 k := bc58_p_mem_box hk0 hk1
  have m1m1 : bc58_p 1 (-1) ∈ box 2 k := bc58_p_mem_box hk1 hkm1
  have m0m1 : bc58_p 0 (-1) ∈ box 2 k := bc58_p_mem_box hk0 hkm1
  rcases bc58_origin_nbr_cases hadj with h | h | h | h
  · rw [h]  
  · 
    rw [h]; exact (bc58_reconnect_around_origin hk ω).symm
  · 
    rw [h]
    have e1 : Connected 2 (removeSite 0 (bc58_boxOpen 2 k ω)) (bc58_p 0 1) (bc58_p 1 1) := by
      have hadj' : (hypercubicLattice 2).Adj (bc58_p 0 1) (bc58_p 1 1) := by
        rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp [bc58_p]
      exact bc58_boxOpen_removeSite_adj_connected m01 m11 hadj'
        (bc58_origin_notMem_edge (by decide) (by decide)) ω
    have e2 : Connected 2 (removeSite 0 (bc58_boxOpen 2 k ω)) (bc58_p 1 1) (bc58_p 1 0) := by
      have hadj' : (hypercubicLattice 2).Adj (bc58_p 1 0) (bc58_p 1 1) := by
        rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp [bc58_p]
      exact (bc58_boxOpen_removeSite_adj_connected m10 m11 hadj'
        (bc58_origin_notMem_edge (by decide) (by decide)) ω).symm
    exact e1.trans e2
  · 
    rw [h]
    have e1 : Connected 2 (removeSite 0 (bc58_boxOpen 2 k ω)) (bc58_p 0 (-1)) (bc58_p 1 (-1)) := by
      have hadj' : (hypercubicLattice 2).Adj (bc58_p 0 (-1)) (bc58_p 1 (-1)) := by
        rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp [bc58_p]
      exact bc58_boxOpen_removeSite_adj_connected m0m1 m1m1 hadj'
        (bc58_origin_notMem_edge (by decide) (by decide)) ω
    have e2 : Connected 2 (removeSite 0 (bc58_boxOpen 2 k ω)) (bc58_p 1 (-1)) (bc58_p 1 0) := by
      have hadj' : (hypercubicLattice 2).Adj (bc58_p 1 0) (bc58_p 1 (-1)) := by
        rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp [bc58_p]
      exact (bc58_boxOpen_removeSite_adj_connected m10 m1m1 hadj'
        (bc58_origin_notMem_edge (by decide) (by decide)) ω).symm
    exact e1.trans e2


theorem bc58_origin_nbrs_connected {k : ℕ} (hk : 1 ≤ k) (ω : ConfigSpace (Sym2 (Site 2)))
    {a b : Site 2} (ha : (hypercubicLattice 2).Adj 0 a) (hb : (hypercubicLattice 2).Adj 0 b) :
    Connected 2 (removeSite 0 (bc58_boxOpen 2 k ω)) a b :=
  (bc58_origin_nbr_connected_to_e hk ω ha).trans
    (bc58_origin_nbr_connected_to_e hk ω hb).symm


theorem bc58_boxOpen_not_classicalTrif {k : ℕ} (hk : 1 ≤ k) (ω : ConfigSpace (Sym2 (Site 2))) :
    ¬ bc47_IsClassicalTrifurcation (bc58_boxOpen 2 k ω) 0 := by
  rintro ⟨a₁, a₂, a₃, ⟨h12, _, _⟩, ⟨he1, he2, _⟩, _, ⟨hsep12, _, _⟩⟩
  
  exact hsep12 (bc58_origin_nbrs_connected hk ω he1.1 he2.1)


theorem bc58_wholeBoxG_not_witness {k : ℕ} (hk : 1 ≤ k) (ω : ConfigSpace (Sym2 (Site 2))) :
    ¬ bc47_IsClassicalTrifurcation
        (forceOpenFinset (bc58_boxInternalEdges 2 k) ω) 0 :=
  bc58_boxOpen_not_classicalTrif hk ω


theorem bc58_evenLines_boxOpen_reconnect {k : ℕ} (hk : 1 ≤ k) :
    ¬ bc47_IsClassicalTrifurcation (bc58_boxOpen 2 k bc57_evenLines) 0 :=
  bc58_boxOpen_not_classicalTrif hk bc57_evenLines


theorem bc58_threeMeet_evenLines : bc57_evenLines ∈ threeMeetBox 2 6 :=
  bc57_mem_threeMeetBox


theorem bc58_status (hd : 1 ≤ d) (p : NNReal) (hp1 : p ≤ 1) (hp0 : 0 < p) :
    
    ((∀ n : ℕ, bc58_OriginTrifModification d n) →
      (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω = 0} = 1 ∨
        bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω = 1} = 1)
        ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0
        ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
            {ω | numInfiniteClusters d ω ≤ 1} = 1) ∧
    
    (∀ {k : ℕ}, 1 ≤ k → ∀ ω : ConfigSpace (Sym2 (Site 2)),
      Connected 2 (removeSite 0 (bc58_boxOpen 2 k ω)) (bc58_p 1 0) (bc58_p (-1) 0)) ∧
    (∀ {k : ℕ}, 1 ≤ k → ∀ ω : ConfigSpace (Sym2 (Site 2)),
      ¬ bc47_IsClassicalTrifurcation (bc58_boxOpen 2 k ω) 0) ∧
    
    (bc57_evenLines ∈ threeMeetBox 2 6) :=
  ⟨fun hmod => bc58_burton_keane_bernoulli_of_originTrifModification hd p hp1 hp0 hmod,
   fun hk ω => bc58_reconnect_around_origin hk ω,
   fun hk ω => bc58_boxOpen_not_classicalTrif hk ω,
   bc58_threeMeet_evenLines⟩

end StatMech.Walls
