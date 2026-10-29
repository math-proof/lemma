/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SingleLeafHallClose.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.ForestLeafCountClose.Part4
import Def.StatisticalMechanics.Code.Percolation.SingleLeafHallClose
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem slh_spanningTreeLeafCount_of_treeForest (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : slh_TreeForestData ω n) :
    flc2_SpanningTreeLeafCount ω n := by
  classical
  obtain ⟨W, _, _, G, _, π, ιT, sec, lamL, hTree, hWcard, hπ, hπinj,
    hπιT, hιinj, hsec, hlammap, hlaminj⟩ := h
  refine ⟨W, inferInstance, inferInstance, G, inferInstance, ιT, lamL, hTree, hWcard,
    ?_, hιinj, hlammap, hlaminj⟩
  
  intro x hxbox htri
  have htri' := htri
  
  obtain ⟨a₁, a₂, a₃, ⟨hne12, hne13, hne23⟩, ⟨hc1, hc2, hc3⟩, _, ⟨hcut12, hcut13, hcut23⟩⟩ := htri'
  set p := ιT x with hp
  have hpx : π p = x := hπιT x hxbox htri
  
  obtain ⟨hπw1, hw1p, hr1⟩ := hsec x hxbox htri a₁ hc1
  obtain ⟨hπw2, hw2p, hr2⟩ := hsec x hxbox htri a₂ hc2
  obtain ⟨hπw3, hw3p, hr3⟩ := hsec x hxbox htri a₃ hc3
  
  have hcutG : ∀ (u v : W) (b c : Site d), π u = b → π v = c →
      (hup : u ≠ p) → (hvp : v ≠ p) →
      ¬ Connected d (removeSite x ω) b c →
      ¬ (G.induce ({p}ᶜ : Set W)).Reachable
        ⟨u, by simpa using hup⟩ ⟨v, by simpa using hvp⟩ := by
    intro u v b c hub hvc hup hvp hcut hreach
    apply hcut
    have := slh_connected_removeSite_of_G_induce π hπ hπinj hup hvp hreach
    rwa [hpx, hub, hvc] at this
  refine slh_deg_ge_three_of_cut hr1 hr2 hr3 hw1p.symm hw2p.symm hw3p.symm
    (hcutG _ _ _ _ hπw1 hπw2 hw1p hw2p hcut12)
    (hcutG _ _ _ _ hπw1 hπw3 hw1p hw3p hcut13)
    (hcutG _ _ _ _ hπw2 hπw3 hw2p hw3p hcut23)


theorem slh_Tcount_le_boundary_of_treeForest (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : slh_TreeForestData ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  flc2_Tcount_le_boundary_of_spanningTree ω n (slh_spanningTreeLeafCount_of_treeForest ω n h)


open Classical in


theorem slh_treeForestData_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {z₀ z₁ : Site d} (hz₀ : z₀ ∈ vertexBoundary d n) (hz₁ : z₁ ∈ vertexBoundary d n)
    (hopen : (openSubgraph d ω).Adj z₀ z₁)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    slh_TreeForestData ω n := by
  classical
  have hzne : z₀ ≠ z₁ := (openSubgraph d ω).ne_of_adj hopen
  refine ⟨Fin 2, inferInstance, inferInstance, Flc2Witness.pathG, inferInstance,
    (fun v => if v = 0 then z₀ else z₁), (fun _ => (0 : Fin 2)), (fun _ _ => (0 : Fin 2)),
    (fun v => if v = 0 then z₀ else z₁), Flc2Witness.pathG_isTree, by decide, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · 
    intro u v huv
    
    have h01 : (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) := by
      revert huv; fin_cases u <;> fin_cases v <;> simp_all <;> decide
    rcases h01 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simpa using hopen
    · simpa using hopen.symm
  · 
    intro u v huv
    fin_cases u <;> fin_cases v <;> simp_all
  · 
    intro x hxbox htri; exact absurd htri (hno x hxbox)
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
    fin_cases u <;> fin_cases v <;> simp_all


theorem slh_claw_survives_branchingCount {W : Type*} [Fintype W] (G : SimpleGraph W)
    [DecidableRel G.Adj] (hTree : G.IsTree) (hWcard : 2 ≤ Fintype.card W) :
    (univ.filter (fun v => 3 ≤ G.degree v)).card
      < (univ.filter (fun v => G.degree v = 1)).card :=
  flc2_tree_internal_lt_leaves G hTree hWcard


theorem slh_burton_keane_bernoulli_of_treeForest (hd : 1 ≤ d) (p : NNReal) (hp1 : p ≤ 1)
    (hp0 : 0 < p)
    (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → slh_TreeForestData ω n)
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
    (fun ω n hn => slh_Tcount_le_boundary_of_treeForest ω n (hres ω n hn))
    (fun n => bkc_boxFinsetBK_card_pos d n)
    (bkc_boundary_vol_tendsto d hd)
    htrif

end Percolation
end StatMech
