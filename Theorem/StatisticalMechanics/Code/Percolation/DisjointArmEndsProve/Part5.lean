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
import Def.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve.Part5
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem daep_cutDisjoint_of_globalCutSeparation (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (h : daep_GlobalCutSeparation ω n) :
    daep_CutDisjointArmEnds ω n := by
  classical
  obtain ⟨b, hb, hsep⟩ := h
  refine ⟨fun x => daep_globalCutArmEnds (tfc_trifFinset ω n) ω n (b x), ?_, ?_, ?_⟩
  · 
    intro x hxbox htri
    obtain ⟨hbbox, _, hbinf⟩ := hb x hxbox htri
    exact daep_globalCutArmEnds_nonempty (tfc_trifFinset ω n) ω n hn (b x) hbbox hbinf
  · 
    intro x hxbox htri z hz
    obtain ⟨_, hbconn, _⟩ := hb x hxbox htri
    refine ⟨(daep_mem_globalCutArmEnds.mp hz).1, ?_⟩
    exact hbconn.trans (daep_globalCutArmEnds_connected (tfc_trifFinset ω n) ω n hz)
  · 
    intro x hxbox htri y hybox htriy hxy
    exact daep_globalCutArmEnds_disjoint_of_disconnected (tfc_trifFinset ω n) ω n
      (hsep x hxbox htri y hybox htriy hxy)


theorem daep_removeSites_singleton (x : Site d) (ω : ConfigSpace (Sym2 (Site d))) :
    removeSites {x} ω = removeSite x ω := by
  funext e
  unfold removeSites removeSite
  by_cases h : x ∈ e
  · rw [if_pos ⟨x, Finset.mem_singleton_self x, h⟩, if_pos h]
  · rw [if_neg (by rintro ⟨t, ht, hte⟩; rw [Finset.mem_singleton] at ht; exact h (ht ▸ hte)),
      if_neg h]


theorem daep_globalCutSeparation_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    daep_GlobalCutSeparation ω n := by
  refine ⟨id, ?_, ?_⟩
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro x hxbox htri _ _ _ _; exact absurd htri (hno x hxbox)


theorem daep_globalCutSeparation_of_uniqueTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ a : Site d} (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (habox : a ∈ box d n) (haconn : Connected d ω x₀ a)
    (hainf : (cluster d (removeSite x₀ ω) a).Infinite)
    (huniq : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀) :
    daep_GlobalCutSeparation ω n := by
  classical
  
  have hT : tfc_trifFinset ω n = {x₀} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨tfc_mem_trifFinset.mpr ⟨hx0box, htri0⟩, ?_⟩
    intro y hy
    rw [tfc_mem_trifFinset] at hy
    exact huniq y hy.1 hy.2
  have hcut : removeSites (tfc_trifFinset ω n) ω = removeSite x₀ ω := by
    rw [hT, daep_removeSites_singleton]
  refine ⟨fun _ => a, ?_, ?_⟩
  · intro x hxbox htri
    have hx0 : x = x₀ := huniq x hxbox htri
    subst hx0
    refine ⟨habox, haconn, ?_⟩
    rw [hcut]; exact hainf
  · intro x hxbox htri y hybox htriy hxy
    exact absurd ((huniq x hxbox htri).trans (huniq y hybox htriy).symm) hxy


theorem daep_Tcount_le_boundary_of_globalCutSeparation (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (hn : 1 ≤ n) (h : daep_GlobalCutSeparation ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  daep_Tcount_le_boundary_of_cutDisjoint ω n (daep_cutDisjoint_of_globalCutSeparation ω n hn h)


theorem daep_burton_keane_bernoulli_of_globalCutSeparation (hd : 1 ≤ d) (p : NNReal) (hp1 : p ≤ 1)
    (hp0 : 0 < p)
    (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      daep_GlobalCutSeparation ω n)
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
  daep_burton_keane_bernoulli hd p hp1 hp0
    (fun ω n hn => daep_cutDisjoint_of_globalCutSeparation ω n hn (hres ω n hn))
    htrif

end Percolation
end StatMech
