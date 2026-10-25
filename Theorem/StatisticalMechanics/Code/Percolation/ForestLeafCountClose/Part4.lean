/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestLeafCountClose.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneClose.Part2
import Instance.StatisticalMechanics.Code.Percolation.ForestLeafCountClose.Part4
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


namespace Flc2Witness

theorem starG_isTree : starG.IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨?_, ?_⟩
  · rw [SimpleGraph.connected_iff_exists_forall_reachable]; exact ⟨0, by decide⟩
  · rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]; decide

theorem starG_centre_deg : starG.degree 0 = 3 := by decide

theorem starG_leaf_deg : ∀ v : Fin 4, v ≠ 0 → starG.degree v = 1 := by decide

theorem starG_deg1_iff (v : Fin 4) : starG.degree v = 1 ↔ v ≠ 0 := by
  constructor
  · intro h; rintro rfl; rw [starG_centre_deg] at h; exact absurd h (by decide)
  · exact starG_leaf_deg v

end Flc2Witness


open Classical in


theorem flc2_spanningTreeLeafCount_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {z₀ z₁ : Site d} (hz₀ : z₀ ∈ vertexBoundary d n) (hz₁ : z₁ ∈ vertexBoundary d n)
    (hzne : z₀ ≠ z₁)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    flc2_SpanningTreeLeafCount ω n := by
  classical
  refine ⟨Fin 2, inferInstance, inferInstance, Flc2Witness.pathG, inferInstance,
    (fun _ => (0 : Fin 2)), (fun v => if v = 0 then z₀ else z₁),
    Flc2Witness.pathG_isTree, by decide, ?_, ?_, ?_, ?_⟩
  · 
    intro x hxbox htri; exact absurd htri (hno x hxbox)
  · 
    intro x hxbox htri; exact absurd htri (hno x hxbox)
  · 
    intro v _; fin_cases v
    · simpa using hz₀
    · simpa using hz₁
  · 
    intro u hu v hv huv
    fin_cases u <;> fin_cases v
    · rfl
    · exact absurd huv hzne
    · exact absurd huv.symm hzne
    · rfl

open Classical in


theorem flc2_spanningTreeLeafCount_star (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {r : Site d} (hrbox : r ∈ box d n) (htri_r : IsTrifurcation d ω r)
    (z : Fin 3 → Site d) (hzb : ∀ i, z i ∈ vertexBoundary d n) (hzinj : Function.Injective z)
    (hsingle : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = r) :
    flc2_SpanningTreeLeafCount ω n := by
  classical
  
  set lamL : Fin 4 → Site d := fun v =>
    if v = 1 then z 0 else if v = 2 then z 1 else if v = 3 then z 2 else z 0 with hlamL
  refine ⟨Fin 4, inferInstance, inferInstance, Flc2Witness.starG, inferInstance,
    (fun _ => (0 : Fin 4)), lamL, Flc2Witness.starG_isTree, by decide, ?_, ?_, ?_, ?_⟩
  · 
    intro x hxbox htri; rw [Flc2Witness.starG_centre_deg]
  · 
    intro x hxbox htri y hybox htriy _
    rw [hsingle x hxbox htri, hsingle y hybox htriy]
  · 
    intro v hv
    rw [Flc2Witness.starG_deg1_iff] at hv
    fin_cases v
    · exact absurd rfl hv
    · simpa [hlamL] using hzb 0
    · simpa [hlamL] using hzb 1
    · simpa [hlamL] using hzb 2
  · 
    intro u hu v hv huv
    rw [Finset.mem_coe, Finset.mem_filter] at hu hv
    rw [Flc2Witness.starG_deg1_iff] at hu hv
    have hu' := hu.2; have hv' := hv.2
    fin_cases u <;> fin_cases v <;>
      first
        | exact absurd rfl hu'
        | exact absurd rfl hv'
        | rfl
        | (revert huv; simp only [hlamL]; intro huv; first
            | (exact absurd (hzinj huv) (by decide))
            | (exact absurd (hzinj huv.symm) (by decide)))


theorem flc2_hbound_of_spanningTree
    (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → flc2_SpanningTreeLeafCount ω n) :
    ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      Tcount d ω n ≤ boxSV_boundaryCard d n :=
  fun ω n hn => flc2_Tcount_le_boundary_of_spanningTree ω n (hres ω n hn)


theorem flc2_burton_keane_bernoulli_of_spanningTree (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1)
    (hp0 : 0 < p)
    (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      flc2_SpanningTreeLeafCount ω n)
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
  tfc_burton_keane_uniqueness_full (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1)
    (bkc_bernoulli_isErgodic hd p hp1)
    (bkc_bernoulli_hasFiniteEnergyMerge p hp1 hp0)
    (fun n => boxSV_boundaryCard d n)
    (flc2_hbound_of_spanningTree hres)
    (fun n => bkc_boxFinsetBK_card_pos d n)
    (bkc_boundary_vol_tendsto d hd)
    htrif

end Percolation
end StatMech
