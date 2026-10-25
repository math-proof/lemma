/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc112sepcontract.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc110globalforest
import Theorem.StatisticalMechanics.Code.Walls.bc106separated.Part3
import Def.StatisticalMechanics.Code.Walls.bc112sepcontract.Part6
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc112_leaf_mem_own_box (hd : 1 ≤ d) {L : ℕ} (hL : 3 ≤ L) (y : Site d) {k : ℤ}
    (hk : k ∈ bc112_shifts) : bc112_leaf hd y k ∈ bc61_boxAround d L y :=
  bc112_leaf_mem_box hd y (bc112_shifts_natAbs_le hk hL)


theorem bc112_leaf_ne_hub (hd : 1 ≤ d) {ω : ConfigSpace (Sym2 (Site d))} {L R : ℕ} (hL : 3 ≤ L)
    {y z : Site d} (hy : y ∈ bc112_hubs ω L R) (hz : z ∈ bc112_hubs ω L R)
    {k : ℤ} (hk : k ∈ bc112_shifts) : bc112_leaf hd y k ≠ z := by
  intro h
  by_cases hyz : y = z
  · subst hyz
    exact bc112_leaf_ne_centre hd y (bc112_shifts_ne_zero hk) h
  · 
    have hleafbox : bc112_leaf hd y k ∈ bc61_boxAround d L y := bc112_leaf_mem_own_box hd hL y hk
    have hzbox : z ∈ bc61_boxAround d L z := bc105_centre_mem_own_box L z
    have hdisj := bc112_hubs_boxes_disjoint hy hz hyz
    rw [h] at hleafbox
    exact (Finset.disjoint_left.mp hdisj hleafbox) hzbox


theorem bc112_leaf_ne_leaf_of_ne_hub (hd : 1 ≤ d) {ω : ConfigSpace (Sym2 (Site d))} {L R : ℕ}
    (hL : 3 ≤ L) {y z : Site d} (hy : y ∈ bc112_hubs ω L R) (hz : z ∈ bc112_hubs ω L R)
    (hyz : y ≠ z) {k k' : ℤ} (hk : k ∈ bc112_shifts) (hk' : k' ∈ bc112_shifts) :
    bc112_leaf hd y k ≠ bc112_leaf hd z k' := by
  intro h
  have h1 : bc112_leaf hd y k ∈ bc61_boxAround d L y := bc112_leaf_mem_own_box hd hL y hk
  have h2 : bc112_leaf hd z k' ∈ bc61_boxAround d L z := bc112_leaf_mem_own_box hd hL z hk'
  have hdisj := bc112_hubs_boxes_disjoint hy hz hyz
  rw [h] at h1
  exact (Finset.disjoint_left.mp hdisj h1) h2


theorem bc112_leaf_same_hub_inj (hd : 1 ≤ d) (y : Site d) {k k' : ℤ}
    (h : bc112_leaf hd y k = bc112_leaf hd y k') : k = k' := by
  by_contra hne
  exact bc112_leaf_inj hd y hne h


theorem bc112_hub_mem_carrier (hd : 1 ≤ d) {ω : ConfigSpace (Sym2 (Site d))} {L R : ℕ} {y : Site d}
    (hy : y ∈ bc112_hubs ω L R) : y ∈ bc112_carrier hd ω L R := by
  classical
  unfold bc112_carrier
  exact Finset.mem_union_left _ hy

theorem bc112_leaf_mem_carrier (hd : 1 ≤ d) {ω : ConfigSpace (Sym2 (Site d))} {L R : ℕ} {y : Site d}
    (hy : y ∈ bc112_hubs ω L R) {k : ℤ} (hk : k ∈ bc112_shifts) :
    bc112_leaf hd y k ∈ bc112_carrier hd ω L R := by
  classical
  unfold bc112_carrier
  apply Finset.mem_union_right
  rw [Finset.mem_biUnion]
  exact ⟨y, hy, Finset.mem_image.mpr ⟨k, hk, rfl⟩⟩


theorem bc112_starRel_leaf_forces_hub (hd : 1 ≤ d) {ω : ConfigSpace (Sym2 (Site d))} {L R : ℕ}
    (hL : 3 ≤ L) {y : Site d} (hy : y ∈ bc112_hubs ω L R) {k : ℤ} (hk : k ∈ bc112_shifts)
    {w : Site d} (h : bc112_starRel hd ω L R (bc112_leaf hd y k) w
      ∨ bc112_starRel hd ω L R w (bc112_leaf hd y k)) :
    w = y := by
  
  have key : ∀ z ∈ bc112_hubs ω L R, ∀ k' ∈ bc112_shifts,
      (bc112_leaf hd y k = z ∧ w = bc112_leaf hd z k') ∨
      (w = z ∧ bc112_leaf hd y k = bc112_leaf hd z k') → w = y := by
    intro z hz k' hk' hcase
    rcases hcase with ⟨heq, _⟩ | ⟨hwz, hleafeq⟩
    · 
      exact absurd heq (bc112_leaf_ne_hub hd hL hy hz hk)
    · 
      by_cases hyz : y = z
      · subst hyz
        
        rw [hwz]
      · exact absurd hleafeq (bc112_leaf_ne_leaf_of_ne_hub hd hL hy hz hyz hk hk')
  rcases h with ⟨z, hz, k', hk', hor⟩ | ⟨z, hz, k', hk', hor⟩
  · 
    rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact key z hz k' hk' (Or.inl ⟨h1, h2⟩)
    · exact key z hz k' hk' (Or.inr ⟨h1, h2⟩)
  · 
    rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · 
      exact key z hz k' hk' (Or.inr ⟨h1, h2⟩)
    · 
      exact key z hz k' hk' (Or.inl ⟨h1, h2⟩)


theorem bc112_starGraph_leaf_adj_forces_hub (hd : 1 ≤ d) {ω : ConfigSpace (Sym2 (Site d))} {L R : ℕ}
    (hL : 3 ≤ L) {y : Site d} (hy : y ∈ bc112_hubs ω L R) {k : ℤ} (hk : k ∈ bc112_shifts)
    {lv w' : ↑(bc112_carrier hd ω L R)} (hlv : (lv : Site d) = bc112_leaf hd y k)
    (hadj : (bc112_starGraph hd ω L R).Adj lv w') : (w' : Site d) = y := by
  rw [bc112_starGraph, SimpleGraph.fromRel_adj] at hadj
  obtain ⟨hne, hrel⟩ := hadj
  rw [hlv] at hrel
  exact bc112_starRel_leaf_forces_hub hd hL hy hk hrel


theorem bc112_leaf_isolated_in_cut (hd : 1 ≤ d) {ω : ConfigSpace (Sym2 (Site d))} {L R : ℕ}
    (hL : 3 ≤ L) {y : Site d} (hy : y ∈ bc112_hubs ω L R) {k : ℤ} (hk : k ∈ bc112_shifts)
    (hub lv : ↑(bc112_carrier hd ω L R)) (hhub : (hub : Site d) = y)
    (hlv : (lv : Site d) = bc112_leaf hd y k)
    (w' : ↑(bc112_carrier hd ω L R)) :
    ¬ ((bc112_starGraph hd ω L R).deleteIncidenceSet hub).Adj lv w' := by
  intro hadj
  rw [deleteIncidenceSet_adj] at hadj
  obtain ⟨hstar, hlvne, hw'ne⟩ := hadj
  
  have : (w' : Site d) = y := bc112_starGraph_leaf_adj_forces_hub hd hL hy hk hlv hstar
  apply hw'ne
  apply Subtype.ext
  rw [this, hhub]


theorem bc112_leaves_not_reachable_in_cut (hd : 1 ≤ d) {ω : ConfigSpace (Sym2 (Site d))} {L R : ℕ}
    (hL : 3 ≤ L) {y : Site d} (hy : y ∈ bc112_hubs ω L R) {k₁ k₂ : ℤ}
    (hk₁ : k₁ ∈ bc112_shifts) (hk₂ : k₂ ∈ bc112_shifts)
    (hub lv₁ lv₂ : ↑(bc112_carrier hd ω L R)) (hhub : (hub : Site d) = y)
    (hlv₁ : (lv₁ : Site d) = bc112_leaf hd y k₁) (hlv₂ : (lv₂ : Site d) = bc112_leaf hd y k₂)
    (hne : lv₁ ≠ lv₂) :
    ¬ ((bc112_starGraph hd ω L R).deleteIncidenceSet hub).Reachable lv₁ lv₂ := by
  intro hreach
  obtain ⟨p⟩ := hreach
  cases p with
  | nil => exact hne rfl
  | @cons _ c _ hadj q =>
    exact bc112_leaf_isolated_in_cut hd hL hy hk₁ hub lv₁ hhub hlv₁ c hadj


theorem bc112_starGraph_hub_adj_leaf (hd : 1 ≤ d) {ω : ConfigSpace (Sym2 (Site d))} {L R : ℕ}
    {y : Site d} (hy : y ∈ bc112_hubs ω L R) {k : ℤ} (hk : k ∈ bc112_shifts)
    (hub lv : ↑(bc112_carrier hd ω L R)) (hhub : (hub : Site d) = y)
    (hlv : (lv : Site d) = bc112_leaf hd y k) :
    (bc112_starGraph hd ω L R).Adj hub lv := by
  rw [bc112_starGraph, SimpleGraph.fromRel_adj]
  refine ⟨?_, Or.inl ?_⟩
  · 
    intro h
    rw [h] at hhub
    rw [hlv] at hhub
    exact bc112_leaf_ne_centre hd y (bc112_shifts_ne_zero hk) hhub
  · 
    rw [hhub, hlv]
    exact ⟨y, hy, k, hk, Or.inl ⟨rfl, rfl⟩⟩

open Classical in


theorem bc112_separatedArmGraph_holds (hd : 1 ≤ d)
    (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (hL : 3 ≤ L) :
    bc112_SeparatedArmGraph ω L R := by
  classical
  by_cases hhubs : (bc112_hubs ω L R).Nonempty
  · 
    obtain ⟨y₀, hy₀⟩ := hhubs
    set S : Set (Site d) := ↑(bc112_carrier hd ω L R) with hS
    haveI hSfin : Fintype (↑S : Type) := (Set.toFinite S).fintype
    have hy₀c : y₀ ∈ bc112_carrier hd ω L R := bc112_hub_mem_carrier hd hy₀
    have hSne : Nonempty (↑S : Type) := ⟨⟨y₀, by rw [hS]; exact_mod_cast hy₀c⟩⟩
    set G : SimpleGraph (↑S : Type) := bc112_starGraph hd ω L R with hG
    haveI hGdec : DecidableRel G.Adj := Classical.decRel _
    
    set base : (↑S : Type) := ⟨y₀, by rw [hS]; exact_mod_cast hy₀c⟩ with hbase
    set ιU : Site d → (↑S : Type) := fun z =>
      if hz : z ∈ bc112_carrier hd ω L R then ⟨z, by rw [hS]; exact_mod_cast hz⟩ else base with hιU
    
    have hιU_hub : ∀ z, z ∈ bc112_hubs ω L R → (ιU z : Site d) = z := by
      intro z hz
      have hzc : z ∈ bc112_carrier hd ω L R := bc112_hub_mem_carrier hd hz
      rw [hιU]; simp only [hzc, dif_pos]
    refine ⟨S, hSfin, hSne, G, hGdec, ιU, ?_, ?_⟩
    · 
      intro z hzbox hztri
      have hzhub : z ∈ bc112_hubs ω L R := bc112_mem_hubs.mpr ⟨hzbox, hztri⟩
      have hιUz : (ιU z : Site d) = z := hιU_hub z hzhub
      
      have h1 : (1 : ℤ) ∈ bc112_shifts := by decide
      have h2 : (2 : ℤ) ∈ bc112_shifts := by decide
      have h3 : (3 : ℤ) ∈ bc112_shifts := by decide
      have hl1c : bc112_leaf hd z 1 ∈ bc112_carrier hd ω L R := bc112_leaf_mem_carrier hd hzhub h1
      have hl2c : bc112_leaf hd z 2 ∈ bc112_carrier hd ω L R := bc112_leaf_mem_carrier hd hzhub h2
      have hl3c : bc112_leaf hd z 3 ∈ bc112_carrier hd ω L R := bc112_leaf_mem_carrier hd hzhub h3
      set v₁ : (↑S : Type) := ⟨bc112_leaf hd z 1, by rw [hS]; exact_mod_cast hl1c⟩ with hv₁
      set v₂ : (↑S : Type) := ⟨bc112_leaf hd z 2, by rw [hS]; exact_mod_cast hl2c⟩ with hv₂
      set v₃ : (↑S : Type) := ⟨bc112_leaf hd z 3, by rw [hS]; exact_mod_cast hl3c⟩ with hv₃
      have hv₁s : (v₁ : Site d) = bc112_leaf hd z 1 := rfl
      have hv₂s : (v₂ : Site d) = bc112_leaf hd z 2 := rfl
      have hv₃s : (v₃ : Site d) = bc112_leaf hd z 3 := rfl
      
      have hv₁₂ : v₁ ≠ v₂ := by
        intro h
        exact bc112_leaf_inj hd z (show (1:ℤ) ≠ 2 by decide) (congrArg Subtype.val h)
      have hv₁₃ : v₁ ≠ v₃ := by
        intro h
        exact bc112_leaf_inj hd z (show (1:ℤ) ≠ 3 by decide) (congrArg Subtype.val h)
      have hv₂₃ : v₂ ≠ v₃ := by
        intro h
        exact bc112_leaf_inj hd z (show (2:ℤ) ≠ 3 by decide) (congrArg Subtype.val h)
      refine ⟨v₁, v₂, v₃, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact bc112_starGraph_hub_adj_leaf hd hzhub h1 (ιU z) v₁ hιUz hv₁s
      · exact bc112_starGraph_hub_adj_leaf hd hzhub h2 (ιU z) v₂ hιUz hv₂s
      · exact bc112_starGraph_hub_adj_leaf hd hzhub h3 (ιU z) v₃ hιUz hv₃s
      · exact bc112_leaves_not_reachable_in_cut hd hL hzhub h1 h2 (ιU z) v₁ v₂ hιUz hv₁s hv₂s hv₁₂
      · exact bc112_leaves_not_reachable_in_cut hd hL hzhub h1 h3 (ιU z) v₁ v₃ hιUz hv₁s hv₃s hv₁₃
      · exact bc112_leaves_not_reachable_in_cut hd hL hzhub h2 h3 (ιU z) v₂ v₃ hιUz hv₂s hv₃s hv₂₃
    · 
      intro z hzbox hztri z' hz'box hz'tri hUeq
      have hzhub : z ∈ bc112_hubs ω L R := bc112_mem_hubs.mpr ⟨hzbox, hztri⟩
      have hz'hub : z' ∈ bc112_hubs ω L R := bc112_mem_hubs.mpr ⟨hz'box, hz'tri⟩
      have : (ιU z : Site d) = (ιU z' : Site d) := by rw [hUeq]
      rw [hιU_hub z hzhub, hιU_hub z' hz'hub] at this
      exact this
  · 
    apply bc112_separatedArmGraph_of_noTrif (z₀ := (0 : Site d))
    intro z hzbox hztri
    exact hhubs ⟨z, bc112_mem_hubs.mpr ⟨hzbox, hztri⟩⟩


end StatMech.Walls
