/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc121trifcount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc112sepcontract.Part7
import Theorem.StatisticalMechanics.Code.Walls.bc118pathmember
import Def.StatisticalMechanics.Code.Walls.bc121trifcount
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc121_leaf_has_neighbour {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {v : V} (hv : G.degree v = 1) : ∃ w, G.Adj v w := by
  classical
  have : (G.neighborFinset v).Nonempty := by
    rw [← Finset.card_pos, SimpleGraph.card_neighborFinset_eq_degree, hv]; exact one_pos
  obtain ⟨w, hw⟩ := this
  exact ⟨w, (SimpleGraph.mem_neighborFinset _ _ _).mp hw⟩


theorem bc121_leaf_neighbour_unique {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {v w w' : V} (hv : G.degree v = 1) (hw : G.Adj v w) (hw' : G.Adj v w') :
    w = w' := by
  classical
  have hcard : (G.neighborFinset v).card = 1 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hv
  have hmemw : w ∈ G.neighborFinset v := (SimpleGraph.mem_neighborFinset _ _ _).mpr hw
  have hmemw' : w' ∈ G.neighborFinset v := (SimpleGraph.mem_neighborFinset _ _ _).mpr hw'
  exact Finset.card_le_one.mp (le_of_eq hcard) w hmemw w' hmemw'


theorem bc121_leaf_delete_reachable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {v w : V} (hdeg : G.degree v = 1) (hvw : G.Adj v w)
    {a b : V} (ha : a ≠ v) (hb : b ≠ v) (hreach : G.Reachable a b) :
    (G.deleteEdges {s(v, w)}).Reachable a b := by
  classical
  obtain ⟨p⟩ := hreach
  
  
  
  suffices H : ∀ (n : ℕ) {x y : V} (q : G.Walk x y), q.length ≤ n → x ≠ v → y ≠ v →
      (G.deleteEdges {s(v, w)}).Reachable x y by
    exact H p.length p le_rfl ha hb
  intro n
  induction n with
  | zero =>
    intro x y q hlen hx hy
    
    rw [Nat.le_zero, SimpleGraph.Walk.length_eq_zero_iff] at hlen
    cases hlen; exact Reachable.refl _
  | succ n ih =>
    intro x y q hlen hx hy
    cases q with
    | nil => exact Reachable.refl _
    | @cons x c y hxc r =>
      
      have hrlen : r.length ≤ n := by
        simp only [SimpleGraph.Walk.length_cons] at hlen; omega
      by_cases hcv : c = v
      · 
        
        have hxv : G.Adj x v := hcv ▸ hxc
        have hxw : x = w := (bc121_leaf_neighbour_unique G hdeg hvw hxv.symm).symm
        cases r with
        | nil => rw [hcv] at hy; exact absurd rfl hy  
        | @cons c e y hce s =>
          have hve : G.Adj v e := hcv ▸ hce
          have hew : e = w := (bc121_leaf_neighbour_unique G hdeg hvw hve).symm
          have hene : e ≠ v := by rw [hew]; exact hvw.ne'
          have hslen : s.length ≤ n := by
            simp only [SimpleGraph.Walk.length_cons] at hrlen; omega
          have hr : (G.deleteEdges {s(v, w)}).Reachable e y := ih s hslen hene hy
          
          have hxe : x = e := by rw [hxw, hew]
          rw [hxe]; exact hr
      · 
        have hedge : (G.deleteEdges {s(v, w)}).Adj x c := by
          rw [SimpleGraph.deleteEdges_adj]
          refine ⟨hxc, ?_⟩
          intro hmem
          rw [Set.mem_singleton_iff, Sym2.eq_iff] at hmem
          rcases hmem with ⟨h1, _⟩ | ⟨_, h2⟩
          · exact hx h1
          · exact hcv h2
        exact (hedge.reachable).trans (ih r hrlen hcv hy)


theorem bc121_deleteEdge_card_lt {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {v w : V} (hvw : G.Adj v w)
    [DecidableRel (G.deleteEdges {s(v, w)}).Adj] :
    (G.deleteEdges {s(v, w)}).edgeFinset.card < G.edgeFinset.card := by
  classical
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset (SimpleGraph.edgeFinset_mono (SimpleGraph.deleteEdges_le _))]
  refine ⟨s(v, w), (SimpleGraph.mem_edgeFinset).mpr hvw, ?_⟩
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_deleteEdges]
  intro hmem
  exact hmem.2 (Set.mem_singleton _)


theorem bc121_deleteEdge_acyclic {V : Type*} (G : SimpleGraph V) (hacyc : G.IsAcyclic)
    (s : Set (Sym2 V)) : (G.deleteEdges s).IsAcyclic :=
  hacyc.anti (SimpleGraph.deleteEdges_le s)


theorem bc121_boundaryAnchored_subforest {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (B : V → Prop) [DecidablePred B] (hacyc : G.IsAcyclic) :
    ∃ (F : SimpleGraph V) (_ : DecidableRel F.Adj),
      F ≤ G ∧ F.IsAcyclic ∧ (∀ v, F.degree v = 1 → B v) ∧
      (∀ a b, B a → B b → G.Reachable a b → F.Reachable a b) := by
  classical
  
  suffices H : ∀ (n : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj], G.IsAcyclic →
      G.edgeFinset.card ≤ n →
      ∃ (F : SimpleGraph V) (_ : DecidableRel F.Adj),
        F ≤ G ∧ F.IsAcyclic ∧ (∀ v, F.degree v = 1 → B v) ∧
        (∀ a b, B a → B b → G.Reachable a b → F.Reachable a b) by
    exact H G.edgeFinset.card G hacyc le_rfl
  intro n
  induction n with
  | zero =>
    
    intro G _ hac hcard
    refine ⟨G, inferInstance, le_refl G, hac, ?_, fun a b _ _ h => h⟩
    intro v hv
    
    exfalso
    obtain ⟨w, hvw⟩ := bc121_leaf_has_neighbour G hv
    have : 1 ≤ G.edgeFinset.card := by
      apply Finset.card_pos.mpr
      exact ⟨s(v, w), (SimpleGraph.mem_edgeFinset).mpr hvw⟩
    omega
  | succ n ih =>
    intro G _ hac hcard
    by_cases hbad : ∃ v, G.degree v = 1 ∧ ¬ B v
    · 
      obtain ⟨v, hvdeg, hvB⟩ := hbad
      obtain ⟨w, hvw⟩ := bc121_leaf_has_neighbour G hvdeg
      have hG'ac : (G.deleteEdges {s(v, w)}).IsAcyclic := bc121_deleteEdge_acyclic G hac _
      have hlt : (G.deleteEdges {s(v, w)}).edgeFinset.card < G.edgeFinset.card :=
        bc121_deleteEdge_card_lt G hvw
      have hle' : (G.deleteEdges {s(v, w)}).edgeFinset.card ≤ n := by omega
      obtain ⟨F, hFdec, hFle, hFac, hFleaf, hFpres⟩ :=
        ih (G.deleteEdges {s(v, w)}) hG'ac hle'
      refine ⟨F, hFdec, le_trans hFle (SimpleGraph.deleteEdges_le _), hFac, hFleaf, ?_⟩
      intro a b hBa hBb hab
      apply hFpres a b hBa hBb
      have hav : a ≠ v := fun h => hvB (h ▸ hBa)
      have hbv : b ≠ v := fun h => hvB (h ▸ hBb)
      exact bc121_leaf_delete_reachable G hvdeg hvw hav hbv hab
    · 
      simp only [not_exists, not_and, not_not] at hbad
      exact ⟨G, inferInstance, le_refl G, hac, fun v hv => hbad v hv, fun a b _ _ h => h⟩


theorem bc121_firstNeighbour_of_reachable {V : Type*} {F : SimpleGraph V} {u t : V}
    (hne : u ≠ t) (hreach : F.Reachable u t) :
    ∃ w, F.Adj u w ∧ (F.deleteIncidenceSet u).Reachable w t := by
  classical
  obtain ⟨p, hp⟩ := hreach.exists_isPath
  cases p with
  | nil => exact absurd rfl hne
  | @cons _ w _ hadjuw q =>
    rw [SimpleGraph.Walk.cons_isPath_iff] at hp
    obtain ⟨hqpath, huq⟩ := hp
    refine ⟨w, hadjuw, ?_⟩
    
    have hqavoid : ∀ x ∈ q.support, x ≠ u := by
      intro x hx hxu; subst hxu; exact huq hx
    
    exact bc103_reachable_deleteIncidence_of_walk_avoiding (le_refl F) u q hqavoid


theorem bc121_deg3_of_three_reached_targets {V : Type*} [Fintype V] (F : SimpleGraph V)
    [DecidableRel F.Adj] {u t₁ t₂ t₃ : V}
    (hne₁ : u ≠ t₁) (hne₂ : u ≠ t₂) (hne₃ : u ≠ t₃)
    (hr₁ : F.Reachable u t₁) (hr₂ : F.Reachable u t₂) (hr₃ : F.Reachable u t₃)
    (hcut₁₂ : ¬ (F.deleteIncidenceSet u).Reachable t₁ t₂)
    (hcut₁₃ : ¬ (F.deleteIncidenceSet u).Reachable t₁ t₃)
    (hcut₂₃ : ¬ (F.deleteIncidenceSet u).Reachable t₂ t₃) :
    3 ≤ F.degree u := by
  classical
  obtain ⟨w₁, hw₁adj, hw₁r⟩ := bc121_firstNeighbour_of_reachable hne₁ hr₁
  obtain ⟨w₂, hw₂adj, hw₂r⟩ := bc121_firstNeighbour_of_reachable hne₂ hr₂
  obtain ⟨w₃, hw₃adj, hw₃r⟩ := bc121_firstNeighbour_of_reachable hne₃ hr₃
  have hw12 : w₁ ≠ w₂ := by
    intro h; apply hcut₁₂; exact hw₁r.symm.trans (h ▸ hw₂r)
  have hw13 : w₁ ≠ w₃ := by
    intro h; apply hcut₁₃; exact hw₁r.symm.trans (h ▸ hw₃r)
  have hw23 : w₂ ≠ w₃ := by
    intro h; apply hcut₂₃; exact hw₂r.symm.trans (h ▸ hw₃r)
  exact bc71_deg3_of_three_neighbours F hw₁adj hw₂adj hw₃adj hw12 hw13 hw23


end StatMech.Walls
