/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc34ray.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc26forest.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc33escaping.Part2
import Def.StatisticalMechanics.Code.Walls.bc34ray.Part3
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc34_TavoidingRayData_of_TavoidingCutArmData (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (rank : Site d → ℕ ×ₗ ℕ) (h : bc34_TavoidingCutArmData ω n rank) :
    bc33_TavoidingRayData ω n rank := by
  classical
  obtain ⟨b, hbdata, hsplit⟩ := h
  refine ⟨b, ?_, hsplit⟩
  intro x hxbox htri
  obtain ⟨hbbox, hbconn, hbinf⟩ := hbdata x hxbox htri
  
  have hbT : b x ∉ (↑(tfc_trifFinset ω n) : Set (Site d)) :=
    ray34_notMem_of_avoidCluster_nonempty hbinf.nonempty
  
  obtain ⟨r, hr0, hinj, hadj, hravoid⟩ :=
    ray34_konig (openSubgraph d (removeSite x ω)) hbT hbinf
  refine ⟨hbbox, hbconn, r, hr0, hinj, hadj, ?_⟩
  intro k
  have := hravoid k
  rwa [Finset.mem_coe] at this


theorem ray34_avoidReach_removeSite_iff_connected_removeSites
    {ω : ConfigSpace (Sym2 (Site d))} {T : Finset (Site d)} {x b w : Site d}
    (hxT : x ∈ T) (hbT : b ∉ (↑T : Set (Site d))) :
    ray34_AvoidReach (openSubgraph d (removeSite x ω)) (↑T) b w ↔
      Connected d (removeSites T ω) b w := by
  classical
  constructor
  · 
    rintro ⟨p, hp⟩
    have hedges : ∀ e, e ∈ p.edges → e ∈ (openSubgraph d (removeSites T ω)).edgeSet := by
      intro e he
      induction e using Sym2.ind with
      | _ u v =>
        have hu : u ∈ p.support := p.fst_mem_support_of_mem_edges he
        have hv : v ∈ p.support := p.snd_mem_support_of_mem_edges he
        have huT : u ∉ (↑T : Set (Site d)) := hp u hu
        have hvT : v ∉ (↑T : Set (Site d)) := hp v hv
        have hadj : (openSubgraph d (removeSite x ω)).Adj u v := p.adj_of_mem_edges he
        obtain ⟨hlat, _hopen⟩ := hadj
        
        have hnoT : ¬ ∃ t ∈ T, t ∈ s(u, v) := by
          rintro ⟨t, htT, hte⟩
          rw [Sym2.mem_iff] at hte
          rcases hte with rfl | rfl
          · exact huT (by rwa [Finset.mem_coe])
          · exact hvT (by rwa [Finset.mem_coe])
        have hxnotin : x ∉ s(u, v) := by
          rw [Sym2.mem_iff]; push Not
          exact ⟨fun h => huT (by rw [Finset.mem_coe]; exact h ▸ hxT),
                 fun h => hvT (by rw [Finset.mem_coe]; exact h ▸ hxT)⟩
        have hωopen : ω s(u, v) = true := by
          have := _hopen
          rwa [removeSite_apply_of_notMem hxnotin] at this
        rw [SimpleGraph.mem_edgeSet, openSubgraph_adj]
        refine ⟨hlat, ?_⟩
        rw [removeSites]; simp only [hnoT, if_false]; exact hωopen
    exact (p.transfer _ hedges).reachable
  · 
    rintro ⟨p⟩
    
    have hsuppT : ∀ u ∈ p.support, u ∉ (↑T : Set (Site d)) := by
      intro u hu huT
      rw [Finset.mem_coe] at huT
      
      rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges] at hu
      rcases hu with rfl | ⟨e, he, hue⟩
      · 
        by_cases hnil : p.Nil
        · have hbu : b = u := hnil.eq
          exact hbT (hbu ▸ Finset.mem_coe.mpr huT)
        · have hw : u ∈ p.support := p.end_mem_support
          rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil hnil] at hw
          obtain ⟨e, he, hue⟩ := hw
          induction e using Sym2.ind with
          | _ a c =>
            have hadj : (openSubgraph d (removeSites T ω)).Adj a c := p.adj_of_mem_edges he
            obtain ⟨_hlat, hopen⟩ := hadj
            have hno : ¬ ∃ t ∈ T, t ∈ s(a, c) := by
              rw [removeSites] at hopen; by_contra hc; rw [if_pos hc] at hopen; exact Bool.noConfusion hopen
            exact hno ⟨u, huT, hue⟩
      · induction e using Sym2.ind with
        | _ a c =>
          have hadj : (openSubgraph d (removeSites T ω)).Adj a c := p.adj_of_mem_edges he
          obtain ⟨_hlat, hopen⟩ := hadj
          have hno : ¬ ∃ t ∈ T, t ∈ s(a, c) := by
            rw [removeSites] at hopen; by_contra hc; rw [if_pos hc] at hopen; exact Bool.noConfusion hopen
          exact hno ⟨u, huT, hue⟩
    have hedges : ∀ e, e ∈ p.edges → e ∈ (openSubgraph d (removeSite x ω)).edgeSet := by
      intro e he
      induction e using Sym2.ind with
      | _ u v =>
        have hadj : (openSubgraph d (removeSites T ω)).Adj u v := p.adj_of_mem_edges he
        obtain ⟨hlat, hopen⟩ := hadj
        have hnoT : ¬ ∃ t ∈ T, t ∈ s(u, v) := by
          rw [removeSites] at hopen; by_contra hc; rw [if_pos hc] at hopen; exact Bool.noConfusion hopen
        have hxnotin : x ∉ s(u, v) := fun hx => hnoT ⟨x, hxT, hx⟩
        have hωopen : ω s(u, v) = true := by
          rw [removeSites] at hopen; simpa only [hnoT, if_false] using hopen
        rw [SimpleGraph.mem_edgeSet, openSubgraph_adj]
        refine ⟨hlat, ?_⟩
        rw [removeSite_apply_of_notMem hxnotin]; exact hωopen
    exact ⟨p.transfer _ hedges, by rw [SimpleGraph.Walk.support_transfer]; exact hsuppT⟩


theorem ray34_avoidCluster_removeSite_eq_cluster_removeSites
    {ω : ConfigSpace (Sym2 (Site d))} {T : Finset (Site d)} {x b : Site d}
    (hxT : x ∈ T) (hbT : b ∉ (↑T : Set (Site d))) :
    ray34_AvoidCluster (openSubgraph d (removeSite x ω)) (↑T) b
      = cluster d (removeSites T ω) b := by
  ext w
  rw [ray34_mem_avoidCluster, mem_cluster,
    ray34_avoidReach_removeSite_iff_connected_removeSites hxT hbT]


theorem bc34_TavoidingRayData_of_globalCutArm (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (rank : Site d → ℕ ×ₗ ℕ)
    (b : Site d → Site d)
    (hbdata : ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite)
    (hsplit : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y → rank x < rank y →
      ¬ Connected d (removeSite y ω) (b y) (b x)) :
    bc33_TavoidingRayData ω n rank := by
  classical
  apply bc34_TavoidingRayData_of_TavoidingCutArmData ω n rank
  refine ⟨b, ?_, hsplit⟩
  intro x hxbox htri
  obtain ⟨hbbox, hbconn, hbinf⟩ := hbdata x hxbox htri
  refine ⟨hbbox, hbconn, ?_⟩
  
  have hxT : x ∈ tfc_trifFinset ω n := tfc_mem_trifFinset.mpr ⟨hxbox, htri⟩
  have hbTf : b x ∉ tfc_trifFinset ω n :=
    stac_infiniteCluster_notMem (tfc_trifFinset ω n) ω hbinf
  have hbT : b x ∉ (↑(tfc_trifFinset ω n) : Set (Site d)) := by
    rw [Finset.mem_coe]; exact hbTf
  
  rw [ray34_avoidCluster_removeSite_eq_cluster_removeSites hxT hbT]
  exact hbinf


theorem bc34_burton_keane_bernoulli_of_globalCutArm (hd : 1 ≤ d) (p : ℝ≥0)
    (hp1 : p ≤ 1) (hp0 : 0 < p)
    (rank : ConfigSpace (Sym2 (Site d)) → ℕ → Site d → ℕ ×ₗ ℕ)
    (bfun : ConfigSpace (Sym2 (Site d)) → ℕ → Site d → Site d)
    (hinj : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ),
      ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
        x ≠ y → Connected d ω x y → rank ω n x ≠ rank ω n y)
    (hbdata : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      ∀ x, x ∈ box d n → IsTrifurcation d ω x →
        bfun ω n x ∈ box d n ∧ Connected d ω x (bfun ω n x) ∧
        (cluster d (removeSites (tfc_trifFinset ω n) ω) (bfun ω n x)).Infinite)
    (hsplit : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
        x ≠ y → Connected d ω x y → rank ω n x < rank ω n y →
        ¬ Connected d (removeSite y ω) (bfun ω n y) (bfun ω n x))
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
  bc33_burton_keane_bernoulli_of_TavoidingRayData hd p hp1 hp0 rank hinj
    (fun ω n hn => bc34_TavoidingRayData_of_globalCutArm ω n (rank ω n) (bfun ω n)
      (hbdata ω n hn) (hsplit ω n hn)) htrif


theorem bc34_TavoidingRayData_of_threeChain_globalCut (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ m g : Site d} (b : Site d → Site d)
    (hx0box : x₀ ∈ box d n) (hmbox : m ∈ box d n) (hgbox : g ∈ box d n)
    (hx0m : x₀ ≠ m) (hx0g : x₀ ≠ g) (hmg : m ≠ g)
    (hthree : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = m ∨ x = g)
    (harm : ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite)
    (hsxm : ¬ Connected d (removeSite m ω) (b m) (b x₀))
    (hsxg : ¬ Connected d (removeSite g ω) (b g) (b x₀))
    (hsmg : ¬ Connected d (removeSite g ω) (b g) (b m)) :
    bc33_TavoidingRayData ω n
      (fun z => if z = x₀ then toLex (0, 0)
                else if z = m then toLex (1, 0) else toLex (2, 0)) := by
  classical
  set dep : Site d → ℕ := fun z => if z = x₀ then 0 else if z = m then 1 else 2 with hdep
  have hdepx0 : dep x₀ = 0 := by simp [hdep]
  have hdepm : dep m = 1 := by simp [hdep, hx0m.symm]
  have hdepg : dep g = 2 := by simp [hdep, hx0g.symm, hmg.symm]
  have hrankeq : (fun z : Site d => if z = x₀ then toLex (0, 0)
        else if z = m then toLex (1, 0) else toLex (2, 0))
      = fun z => toLex (dep z, 0) := by
    funext z; simp only [hdep]; split_ifs <;> rfl
  rw [show (fun z : Site d => if z = x₀ then toLex (0, 0)
        else if z = m then toLex (1, 0) else toLex (2, 0))
      = fun z => toLex (dep z, 0) from hrankeq]
  apply bc34_TavoidingRayData_of_globalCutArm ω n _ b harm
  intro x hxbox htri y hybox htriy hxy _ hlt
  rcases hthree x hxbox htri with rfl | rfl | rfl <;>
    rcases hthree y hybox htriy with rfl | rfl | rfl
  · exact absurd rfl hxy
  · exact hsxm
  · exact hsxg
  · rw [hdepm, hdepx0] at hlt
    exact absurd hlt (stt_lex_not_lt_fst (by norm_num))
  · exact absurd rfl hxy
  · exact hsmg
  · rw [hdepg, hdepx0] at hlt
    exact absurd hlt (stt_lex_not_lt_fst (by norm_num))
  · rw [hdepg, hdepm] at hlt
    exact absurd hlt (stt_lex_not_lt_fst (by norm_num))
  · exact absurd rfl hxy

end StatMech.Walls
