/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestLeafDisjointClose.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.BKForestLib.Part6
import Theorem.StatisticalMechanics.Code.Percolation.BKHallSDRClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SpanningTreeArmClose.Part3
import Theorem.StatisticalMechanics.Code.Percolation.ArmEndDisjointClose.Part4
import Def.StatisticalMechanics.Code.Percolation.ForestLeafDisjointClose
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem fld_outwardArm_of_forestPeel (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bkfl_ForestPeel ω n) : fld_OutwardArm ω n := by
  intro x hxbox htri
  obtain ⟨a, hdata, hunocc, hfar⟩ := h x hxbox htri
  exact ⟨a, hdata, bkfl_free_of_unoccupied ω (tfc_trifFinset ω n) hunocc, hfar⟩


theorem fld_forestPeel_of_outwardArm (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : fld_OutwardArm ω n) : bkfl_ForestPeel ω n := by
  intro x hxbox htri
  obtain ⟨a, hdata, hout, hfar⟩ := h x hxbox htri
  refine ⟨a, hdata, ?_, hfar⟩
  rintro ⟨y, hyT, hyx, hcy⟩
  exact hout y hyT hyx hcy


theorem fld_outwardArm_iff_forestPeel (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    fld_OutwardArm ω n ↔ bkfl_ForestPeel ω n :=
  ⟨fld_forestPeel_of_outwardArm ω n, fld_outwardArm_of_forestPeel ω n⟩


theorem fld_globalForestArms_of_outwardArm (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : fld_OutwardArm ω n) : aed_GlobalForestArms ω n := by
  classical
  
  set b : Site d → Site d := fun x =>
    if hx : x ∈ box d n ∧ IsTrifurcation d ω x then (h x hx.1 hx.2).choose else x with hb
  have hbval : ∀ x (hxbox : x ∈ box d n) (htri : IsTrifurcation d ω x),
      b x = (h x hxbox htri).choose := by
    intro x hxbox htri
    simp only [hb, dif_pos (⟨hxbox, htri⟩ : x ∈ box d n ∧ IsTrifurcation d ω x)]
  refine ⟨b, ?_, ?_⟩
  · 
    intro x hxbox htri
    have hspec := (h x hxbox htri).choose_spec
    rw [hbval x hxbox htri]; exact hspec.1
  · 
    intro x hxbox htri y hybox htriy hxy
    have hspecx := (h x hxbox htri).choose_spec
    have hspecy := (h y hybox htriy).choose_spec
    have hxT : x ∈ tfc_trifFinset ω n := tfc_mem_trifFinset.mpr ⟨hxbox, htri⟩
    have hyT : y ∈ tfc_trifFinset ω n := tfc_mem_trifFinset.mpr ⟨hybox, htriy⟩
    
    have haout : ∀ z ∈ tfc_trifFinset ω n, z ≠ x →
        ¬ Connected d (removeSite x ω) (b x) z := by
      rw [hbval x hxbox htri]; exact hspecx.2.1
    have hfar : Connected d (removeSite x ω) (b y) y := by
      rw [hbval y hybox htriy]; exact hspecy.2.2 x hxT hxy
    
    exact fld_separate_of_outward_far ω n hxT hyT hxy haout hfar


theorem fld_armEnds_disjoint_of_outward (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x y a a' : Site d}
    (hxT : x ∈ tfc_trifFinset ω n) (hyT : y ∈ tfc_trifFinset ω n) (hxy : x ≠ y)
    (haout : ∀ z ∈ tfc_trifFinset ω n, z ≠ x → ¬ Connected d (removeSite x ω) a z)
    (hfar : Connected d (removeSite x ω) a' y) :
    Disjoint (daep_globalCutArmEnds (tfc_trifFinset ω n) ω n a)
      (daep_globalCutArmEnds (tfc_trifFinset ω n) ω n a') :=
  daep_globalCutArmEnds_disjoint_of_disconnected (tfc_trifFinset ω n) ω n
    (fld_separate_of_outward_far ω n hxT hyT hxy haout hfar)


theorem fld_Tcount_le_boundary_of_outwardArm (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (h : fld_OutwardArm ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  aed_Tcount_le_boundary_of_globalForestArms ω n hn (fld_globalForestArms_of_outwardArm ω n h)


theorem fld_burton_keane_bernoulli_of_outwardArm (hd : 1 ≤ d) (p : NNReal) (hp1 : p ≤ 1)
    (hp0 : 0 < p)
    (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → fld_OutwardArm ω n)
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
  aed_burton_keane_bernoulli_of_globalForestArms hd p hp1 hp0
    (fun ω n hn => fld_globalForestArms_of_outwardArm ω n (hres ω n hn))
    htrif


theorem fld_outwardArm_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    fld_OutwardArm ω n :=
  fld_outwardArm_of_forestPeel ω n (bkfl_forestPeel_of_noTrif ω n hno)


theorem fld_outwardArm_of_uniqueTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ a : Site d} (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (habox : a ∈ box d n) (haconn : Connected d ω x₀ a)
    (hainf : (cluster d (removeSite x₀ ω) a).Infinite)
    (huniq : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀) :
    fld_OutwardArm ω n :=
  fld_outwardArm_of_forestPeel ω n
    (bkfl_forestPeel_of_uniqueTrif ω n hx0box htri0 habox haconn hainf huniq)


theorem fld_outwardArm_of_distinctClusters (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (arm : Site d → Site d)
    (hdata : ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      arm x ∈ box d n ∧ Connected d ω x (arm x) ∧
        (cluster d (removeSites (tfc_trifFinset ω n) ω) (arm x)).Infinite)
    (hfar : ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      ∀ z ∈ tfc_trifFinset ω n, z ≠ x → Connected d (removeSite z ω) (arm x) x)
    (hsep : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n →
      IsTrifurcation d ω y → x ≠ y → ¬ Connected d ω x y) :
    fld_OutwardArm ω n :=
  fld_outwardArm_of_forestPeel ω n
    (bkfl_forestPeel_of_distinctClusters ω n arm hdata hfar hsep)


theorem fld_outwardArm_of_twoTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
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
    fld_OutwardArm ω n :=
  fld_outwardArm_of_forestPeel ω n
    (bkfl_forestPeel_of_twoTrif ω n arm hx0y0 htwo hdata_x hdata_y hocc_x hocc_y hfar_x hfar_y)

end Percolation
end StatMech
