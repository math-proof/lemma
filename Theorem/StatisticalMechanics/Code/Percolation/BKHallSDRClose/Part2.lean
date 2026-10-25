/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BKHallSDRClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneMerge.Part4
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneClose2.Part3
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve.Part5
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve2.Part3
import Def.StatisticalMechanics.Code.Percolation.BKHallSDRClose
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem bhs_distinctArmEnds_of_hall (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bhs_HallArmEnds ω n) :
    tfc_DistinctArmEnds ω n := by
  classical
  obtain ⟨b, hexist, hHall⟩ := h
  set T := tfc_trifFinset ω n with hT
  set armEnds : Site d → Finset (Site d) :=
    fun x => daep_globalCutArmEnds T ω n (b x) with harm
  
  obtain ⟨φ, hφmem, hφinj⟩ := bhs_exists_injOn_of_hall T armEnds hHall
  refine ⟨φ, ?_, ?_⟩
  · 
    intro x hxbox htri
    have hxT : x ∈ T := tfc_mem_trifFinset.mpr ⟨hxbox, htri⟩
    have hmem := hφmem x hxT
    rw [harm, daep_mem_globalCutArmEnds] at hmem
    obtain ⟨_, hbconn, _⟩ := hexist x hxbox htri
    refine ⟨hmem.1, ?_⟩
    
    exact hbconn.trans (connected_mono (daep_removeSites_le T ω) hmem.2)
  · 
    intro x hxbox htri y hybox htriy hxy
    have hxT : x ∈ T := tfc_mem_trifFinset.mpr ⟨hxbox, htri⟩
    have hyT : y ∈ T := tfc_mem_trifFinset.mpr ⟨hybox, htriy⟩
    exact hφinj hxT hyT hxy


theorem bhs_Tcount_le_boundary_of_hall (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bhs_HallArmEnds ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  tfc_Tcount_le_boundary_of_distinctArmEnds ω n (bhs_distinctArmEnds_of_hall ω n h)


theorem bhs_hallArmEnds_of_globalCutSeparation (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (h : daep_GlobalCutSeparation ω n) :
    bhs_HallArmEnds ω n := by
  classical
  obtain ⟨b, hexist, hsep⟩ := h
  refine ⟨b, hexist, ?_⟩
  set T := tfc_trifFinset ω n with hT
  
  apply bhs_hall_of_pairwiseDisjoint T
    (fun x => daep_globalCutArmEnds T ω n (b x))
  · 
    intro x hxT
    rw [hT, tfc_mem_trifFinset] at hxT
    obtain ⟨hbbox, _, hbinf⟩ := hexist x hxT.1 hxT.2
    exact daep_globalCutArmEnds_nonempty T ω n hn (b x) hbbox hbinf
  · 
    intro x hxT y hyT hxy
    rw [hT, tfc_mem_trifFinset] at hxT hyT
    exact daep_globalCutArmEnds_disjoint_of_disconnected T ω n
      (hsep x hxT.1 hxT.2 y hyT.1 hyT.2 hxy)


theorem bhs_hallArmEnds_of_singleCut (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n)
    (h : daep2_SingleCutBranchSeparation ω n) :
    bhs_HallArmEnds ω n :=
  bhs_hallArmEnds_of_globalCutSeparation ω n hn
    (daep2_globalCutSeparation_of_sameCluster ω n
      (daep2_sameClusterCutSeparation_of_singleCut ω n h))


theorem bhs_hallArmEnds_of_disjointSep (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n)
    (b : Site d → Site d)
    (hexist : ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite)
    (hsep : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n →
      IsTrifurcation d ω y → x ≠ y →
      ¬ Connected d (removeSites (tfc_trifFinset ω n) ω) (b x) (b y)) :
    bhs_HallArmEnds ω n :=
  bhs_hallArmEnds_of_globalCutSeparation ω n hn ⟨b, hexist, hsep⟩


theorem bhs_hallArmEnds_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    bhs_HallArmEnds ω n := by
  classical
  refine ⟨id, ?_, ?_⟩
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro S hS
    
    have hTempty : tfc_trifFinset ω n = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro x hx
      rw [tfc_mem_trifFinset] at hx
      exact hno x hx.1 hx.2
    rw [hTempty] at hS
    rw [Finset.subset_empty.mp hS, Finset.card_empty]
    exact Nat.zero_le _


theorem bhs_burton_keane_bernoulli_of_hall (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → bhs_HallArmEnds ω n)
    (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω = ⊤} →
        0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | IsTrifurcation d ω 0}) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  
  tfc_burton_keane_bernoulli hd p hp1 hp0
    (fun ω n _hn => bhs_distinctArmEnds_of_hall ω n (hres ω n _hn))
    htrif

end Percolation
end StatMech
