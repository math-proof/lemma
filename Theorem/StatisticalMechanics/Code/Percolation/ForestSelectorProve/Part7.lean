/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestSelectorProve.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsFinal.Part2
import Theorem.StatisticalMechanics.Code.Percolation.PrivateArmProve.Part2
import Theorem.StatisticalMechanics.Code.Percolation.BKForestLib.Part6
import Def.StatisticalMechanics.Code.Percolation.ForestSelectorProve.Part6
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem fsp_armPlacement_of_divergence (ω : ConfigSpace (Sym2 (Site d)))
    (b : Site d → Site d) {x y : Site d}
    (hbxx : b x ≠ x) (hbyx : x ≠ b y)
    (hxbx : Connected d ω x (b x)) (hxby : Connected d ω x (b y))
    (hdiv : ¬ fsp_sameArm ω x (b x) (b y)) :
    fsp_ArmPlacement ω b x y := by
  refine ⟨fsp_armWitness ω x (b x), fsp_armWitness ω x (b y), hdiv, ?_, ?_⟩
  · exact fsp_armWitness_inArm ω hxbx (Ne.symm hbxx)
  · exact fsp_armWitness_inArm ω hxby hbyx


theorem fsp_rootedArmOrder_of_divergentArmOrder (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : fsp_DivergentArmOrder ω n) : fsp_RootedArmOrder ω n := by
  obtain ⟨b, hdata, hdiv⟩ := h
  refine ⟨b, ?_, ?_⟩
  · intro x hxbox htri
    obtain ⟨hbox, _, hconn, hinf⟩ := hdata x hxbox htri
    exact ⟨hbox, hconn, hinf⟩
  · intro x hxbox htri y hybox htriy hxy hconn
    obtain ⟨_, hbxx, hxbx, _⟩ := hdata x hxbox htri
    obtain ⟨_, hbyy, hyby, _⟩ := hdata y hybox htriy
    
    have hxby : Connected d ω x (b y) := hconn.trans hyby
    
    
    
    
    by_cases hcase : x = b y
    · 
      
      
      
      
      refine ⟨fsp_armWitness ω x (b x), fsp_armWitness ω x (b y),
        hdiv x hxbox htri y hybox htriy hxy hconn, ?_, ?_⟩
      · exact fsp_armWitness_inArm ω hxbx (Ne.symm hbxx)
      · 
        
        have hwit : fsp_armWitness ω x (b y) = x := by
          rw [← hcase]; simp only [fsp_armWitness]
          rw [dif_neg (by rintro ⟨_, hne⟩; exact hne rfl)]
        show Connected d (removeSite x ω) (fsp_armWitness ω x (b y)) (b y)
        rw [hwit, ← hcase]
    · exact fsp_armPlacement_of_divergence ω b hbxx hcase hxbx hxby
        (hdiv x hxbox htri y hybox htriy hxy hconn)


theorem fsp_rootedArmOrder_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    fsp_RootedArmOrder ω n := by
  refine ⟨id, ?_, ?_⟩
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro x hxbox htri; exact absurd htri (hno x hxbox)


theorem fsp_rootedArmOrder_of_uniqueTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ a : Site d} (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (habox : a ∈ box d n) (haconn : Connected d ω x₀ a)
    (hainf : (cluster d (removeSite x₀ ω) a).Infinite)
    (huniq : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀) :
    fsp_RootedArmOrder ω n := by
  classical
  have hT : tfc_trifFinset ω n = {x₀} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨tfc_mem_trifFinset.mpr ⟨hx0box, htri0⟩, ?_⟩
    intro y hy; rw [tfc_mem_trifFinset] at hy; exact huniq y hy.1 hy.2
  have hcut : removeSites (tfc_trifFinset ω n) ω = removeSite x₀ ω := by
    rw [hT, daep_removeSites_singleton]
  refine ⟨fun _ => a, ?_, ?_⟩
  · intro x hxbox htri
    have hx0 : x = x₀ := huniq x hxbox htri
    subst hx0
    refine ⟨habox, haconn, ?_⟩
    rw [hcut]; exact hainf
  · intro x hxbox htri y hybox htriy hxy _
    exact absurd ((huniq x hxbox htri).trans (huniq y hybox htriy).symm) hxy


theorem fsp_rootedArmOrder_of_twoTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ y₀ : Site d} (b : Site d → Site d)
    (hx0y0 : x₀ ≠ y₀)
    (htwo : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = y₀)
    (hdata_x : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
    (hdata_y : b y₀ ∈ box d n ∧ Connected d ω y₀ (b y₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b y₀)).Infinite)
    (hplace_xy : fsp_ArmPlacement ω b x₀ y₀)
    (hplace_yx : fsp_ArmPlacement ω b y₀ x₀) :
    fsp_RootedArmOrder ω n := by
  classical
  refine ⟨b, ?_, ?_⟩
  · intro x hxbox htri
    rcases htwo x hxbox htri with rfl | rfl
    · exact hdata_x
    · exact hdata_y
  · intro x hxbox htri y hybox htriy hxy _
    rcases htwo x hxbox htri with rfl | rfl
    · rcases htwo y hybox htriy with rfl | rfl
      · exact absurd rfl hxy
      · exact hplace_xy
    · rcases htwo y hybox htriy with rfl | rfl
      · exact hplace_yx
      · exact absurd rfl hxy


theorem fsp_divergentArmOrder_of_twoTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ y₀ : Site d} (b : Site d → Site d)
    (hx0y0 : x₀ ≠ y₀)
    (htwo : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = y₀)
    (hdata_x : b x₀ ∈ box d n ∧ b x₀ ≠ x₀ ∧ Connected d ω x₀ (b x₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
    (hdata_y : b y₀ ∈ box d n ∧ b y₀ ≠ y₀ ∧ Connected d ω y₀ (b y₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b y₀)).Infinite)
    (hdiv_xy : ¬ fsp_sameArm ω x₀ (b x₀) (b y₀))
    (hdiv_yx : ¬ fsp_sameArm ω y₀ (b y₀) (b x₀)) :
    fsp_DivergentArmOrder ω n := by
  classical
  refine ⟨b, ?_, ?_⟩
  · intro x hxbox htri
    rcases htwo x hxbox htri with rfl | rfl
    · exact hdata_x
    · exact hdata_y
  · intro x hxbox htri y hybox htriy hxy _
    rcases htwo x hxbox htri with rfl | rfl
    · rcases htwo y hybox htriy with rfl | rfl
      · exact absurd rfl hxy
      · exact hdiv_xy
    · rcases htwo y hybox htriy with rfl | rfl
      · exact hdiv_yx
      · exact absurd rfl hxy


theorem fsp_Tcount_le_boundary_of_treeSelector (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (h : fsp_TreeSelector ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  daep2_Tcount_le_boundary_of_singleCut ω n hn (fsp_singleCut_of_treeSelector ω n h)


theorem fsp_Tcount_le_boundary_of_rootedArmOrder (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (h : fsp_RootedArmOrder ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  fsp_Tcount_le_boundary_of_treeSelector ω n hn (fsp_treeSelector_of_rootedArmOrder ω n h)


theorem fsp_burton_keane_bernoulli_of_treeSelector (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1)
    (hp0 : 0 < p)
    (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → fsp_TreeSelector ω n)
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
  daep2_burton_keane_bernoulli_of_singleCut hd p hp1 hp0
    (fun ω n hn => fsp_singleCut_of_treeSelector ω n (hres ω n hn))
    htrif


theorem fsp_burton_keane_bernoulli_of_rootedArmOrder (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1)
    (hp0 : 0 < p)
    (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → fsp_RootedArmOrder ω n)
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
  fsp_burton_keane_bernoulli_of_treeSelector hd p hp1 hp0
    (fun ω n hn => fsp_treeSelector_of_rootedArmOrder ω n (hres ω n hn))
    htrif


theorem fsp_Tcount_le_boundary_of_divergentArmOrder (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (h : fsp_DivergentArmOrder ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  fsp_Tcount_le_boundary_of_rootedArmOrder ω n hn
    (fsp_rootedArmOrder_of_divergentArmOrder ω n h)


theorem fsp_burton_keane_bernoulli_of_divergentArmOrder (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1)
    (hp0 : 0 < p)
    (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → fsp_DivergentArmOrder ω n)
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
  fsp_burton_keane_bernoulli_of_rootedArmOrder hd p hp1 hp0
    (fun ω n hn => fsp_rootedArmOrder_of_divergentArmOrder ω n (hres ω n hn))
    htrif

end Percolation
end StatMech
