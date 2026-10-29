/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BKForestLib.lean -/

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
import Def.StatisticalMechanics.Code.Percolation.BKForestLib.Part6
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem bkfl_existsPrivateArm_of_forestPeel (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bkfl_ForestPeel ω n) : bkfl_ExistsPrivateArm ω n := by
  intro x hxbox htri
  obtain ⟨a, hdata, hunocc, hfar⟩ := h x hxbox htri
  exact ⟨a, bkfl_pointwise_of_unoccupiedArm ω n (tfc_trifFinset ω n) hdata hunocc hfar⟩


theorem bkfl_privateArm_of_forestPeel (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bkfl_ForestPeel ω n) : daepf_PrivateArm ω n :=
  bkfl_privateArm_of_existsPrivateArm ω n (bkfl_existsPrivateArm_of_forestPeel ω n h)


theorem bkfl_Tcount_le_boundary_of_forestPeel (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (h : bkfl_ForestPeel ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  bkfl_Tcount_le_boundary_of_existsPrivateArm ω n hn
    (bkfl_existsPrivateArm_of_forestPeel ω n h)


theorem bkfl_forestPeel_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    bkfl_ForestPeel ω n := by
  intro x hxbox htri
  exact absurd htri (hno x hxbox)


theorem bkfl_forestPeel_of_uniqueTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ a : Site d} (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (habox : a ∈ box d n) (haconn : Connected d ω x₀ a)
    (hainf : (cluster d (removeSite x₀ ω) a).Infinite)
    (huniq : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀) :
    bkfl_ForestPeel ω n := by
  classical
  have hT : tfc_trifFinset ω n = {x₀} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨tfc_mem_trifFinset.mpr ⟨hx0box, htri0⟩, ?_⟩
    intro y hy; rw [tfc_mem_trifFinset] at hy; exact huniq y hy.1 hy.2
  have hcut : removeSites (tfc_trifFinset ω n) ω = removeSite x₀ ω := by
    rw [hT, daep_removeSites_singleton]
  intro x hxbox htri
  have hx0 : x = x₀ := huniq x hxbox htri
  subst hx0
  refine ⟨a, ⟨habox, haconn, ?_⟩, ?_, ?_⟩
  · rw [hcut]; exact hainf
  · 
    rintro ⟨y, hyT, hyx, _⟩
    rw [hT, Finset.mem_singleton] at hyT
    exact hyx hyT
  · 
    intro z hzT hzx
    rw [hT, Finset.mem_singleton] at hzT
    exact absurd hzT hzx


theorem bkfl_forestPeel_of_distinctClusters (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (arm : Site d → Site d)
    (hdata : ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      arm x ∈ box d n ∧ Connected d ω x (arm x) ∧
        (cluster d (removeSites (tfc_trifFinset ω n) ω) (arm x)).Infinite)
    (hfar : ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      ∀ z ∈ tfc_trifFinset ω n, z ≠ x → Connected d (removeSite z ω) (arm x) x)
    (hsep : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n →
      IsTrifurcation d ω y → x ≠ y → ¬ Connected d ω x y) :
    bkfl_ForestPeel ω n := by
  intro x hxbox htri
  refine ⟨arm x, hdata x hxbox htri, ?_, hfar x hxbox htri⟩
  
  rintro ⟨y, hyT, hyx, hcy⟩
  rw [tfc_mem_trifFinset] at hyT
  
  have hxa : Connected d ω x (arm x) := (hdata x hxbox htri).2.1
  have hay : Connected d ω (arm x) y := connected_mono (by
    intro e; unfold removeSite; by_cases h : x ∈ e
    · rw [if_pos h]; exact Bool.false_le _
    · rw [if_neg h]) hcy
  exact hsep x hxbox htri y hyT.1 hyT.2 (Ne.symm hyx) (hxa.trans hay)


theorem bkfl_forestPeel_of_twoTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ y₀ : Site d} (arm : Site d → Site d)
    (hx0y0 : x₀ ≠ y₀)
    (htwo : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = y₀)
    (hdata_x : arm x₀ ∈ box d n ∧ Connected d ω x₀ (arm x₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (arm x₀)).Infinite)
    (hdata_y : arm y₀ ∈ box d n ∧ Connected d ω y₀ (arm y₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (arm y₀)).Infinite)
    (hocc_x : ¬ Connected d (removeSite x₀ ω) (arm x₀) y₀)
    (hocc_y : ¬ Connected d (removeSite y₀ ω) (arm y₀) x₀)
    (hfar_x : Connected d (removeSite y₀ ω) (arm x₀) x₀)
    (hfar_y : Connected d (removeSite x₀ ω) (arm y₀) y₀) :
    bkfl_ForestPeel ω n := by
  classical
  intro x hxbox htri
  rcases htwo x hxbox htri with rfl | rfl
  · 
    refine ⟨arm x, hdata_x, ?_, ?_⟩
    · 
      rintro ⟨w, hwT, hwx, hcw⟩
      rw [tfc_mem_trifFinset] at hwT
      rcases htwo w hwT.1 hwT.2 with rfl | rfl
      · exact hwx rfl
      · exact hocc_x hcw
    · 
      intro z hzT hzx
      rw [tfc_mem_trifFinset] at hzT
      rcases htwo z hzT.1 hzT.2 with rfl | rfl
      · exact absurd rfl hzx
      · exact hfar_x
  · 
    refine ⟨arm x, hdata_y, ?_, ?_⟩
    · rintro ⟨w, hwT, hwy, hcw⟩
      rw [tfc_mem_trifFinset] at hwT
      rcases htwo w hwT.1 hwT.2 with rfl | rfl
      · exact hocc_y hcw
      · exact hwy rfl
    · intro z hzT hzy
      rw [tfc_mem_trifFinset] at hzT
      rcases htwo z hzT.1 hzT.2 with rfl | rfl
      · exact hfar_y
      · exact absurd rfl hzy


theorem bkfl_burton_keane_bernoulli_of_forestPeel (hd : 1 ≤ d) (p : NNReal) (hp1 : p ≤ 1)
    (hp0 : 0 < p)
    (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → bkfl_ForestPeel ω n)
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
  daepf_burton_keane_bernoulli_of_privateArm hd p hp1 hp0
    (fun ω n hn => bkfl_privateArm_of_forestPeel ω n (hres ω n hn))
    htrif

end Percolation
end StatMech
