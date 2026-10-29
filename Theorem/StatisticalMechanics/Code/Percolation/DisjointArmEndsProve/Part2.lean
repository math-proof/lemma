/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsProve.lean -/

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
import Def.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve.Part2
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem daep_distinctArmEnds_of_cutDisjoint (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : daep_CutDisjointArmEnds ω n) :
    tfc_DistinctArmEnds ω n := by
  classical
  obtain ⟨A, hne, hmem, hdisj⟩ := h
  
  set sel : Site d → Site d := fun x =>
    if hx : x ∈ box d n ∧ IsTrifurcation d ω x then (hne x hx.1 hx.2).choose else x with hsel
  refine ⟨sel, ?_, ?_⟩
  · intro x hxbox htri
    have hchoose := (hne x hxbox htri).choose_spec
    have := hmem x hxbox htri _ hchoose
    simp only [hsel, dif_pos (⟨hxbox, htri⟩ : x ∈ box d n ∧ IsTrifurcation d ω x)]
    exact this
  · intro x hxbox htri y hybox htriy hxy
    by_contra hne'
    have hxchoose := (hne x hxbox htri).choose_spec
    have hychoose := (hne y hybox htriy).choose_spec
    simp only [hsel, dif_pos (⟨hxbox, htri⟩ : x ∈ box d n ∧ IsTrifurcation d ω x),
      dif_pos (⟨hybox, htriy⟩ : y ∈ box d n ∧ IsTrifurcation d ω y)] at hxy
    have hmem' : (hne x hxbox htri).choose ∈ A x ∩ A y :=
      Finset.mem_inter.mpr ⟨hxchoose, hxy ▸ hychoose⟩
    rw [Finset.disjoint_iff_inter_eq_empty.mp (hdisj x hxbox htri y hybox htriy hne')] at hmem'
    exact absurd hmem' (Finset.notMem_empty _)


theorem daep_Tcount_le_boundary_of_cutDisjoint (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : daep_CutDisjointArmEnds ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  tfc_Tcount_le_boundary_of_distinctArmEnds ω n (daep_distinctArmEnds_of_cutDisjoint ω n h)


theorem daep_cutDisjoint_of_subsingleton (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n)
    (hsub : ∀ x y, x ∈ box d n → IsTrifurcation d ω x → y ∈ box d n →
      IsTrifurcation d ω y → x = y) :
    daep_CutDisjointArmEnds ω n := by
  classical
  refine ⟨bk2_armEndFinset ω n, ?_, ?_, ?_⟩
  · intro x hxbox htri
    exact bk2_armEndFinset_nonempty ω n hn x hxbox htri
  · intro x _ _ z hz
    exact bk2_mem_armEndFinset.mp hz
  · intro x hxbox htri y hybox htriy hxy
    exact absurd (hsub x y hxbox htri hybox htriy) hxy


theorem daep_cutDisjoint_of_disjointArmEnds (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (hdisj : bk2_DisjointArmEnds ω n) :
    daep_CutDisjointArmEnds ω n := by
  classical
  refine ⟨bk2_armEndFinset ω n, ?_, ?_, ?_⟩
  · intro x hxbox htri
    exact bk2_armEndFinset_nonempty ω n hn x hxbox htri
  · intro x _ _ z hz
    exact bk2_mem_armEndFinset.mp hz
  · intro x hxbox htri y hybox htriy hxy
    exact hdisj x hxbox htri y hybox htriy hxy


theorem daep_burton_keane_bernoulli (hd : 1 ≤ d) (p : NNReal) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      daep_CutDisjointArmEnds ω n)
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
    (fun ω n hn => daep_distinctArmEnds_of_cutDisjoint ω n (hres ω n hn))
    htrif


end Percolation
end StatMech
