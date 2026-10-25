/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerFaces2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.Cyclomatic.Part2
import Def.StatisticalMechanics.Code.Lattice.EulerFaces2
open SimpleGraph Set


set_option linter.unusedSectionVars false


namespace StatMech.Lattice

variable {V : Type*}


variable [Finite V] [DecidableEq V]


theorem faceCount_sup_edge_of_reachable (G : SimpleGraph V) {a b : V} (hne : a ≠ b)
    (hadj : ¬ G.Adj a b) (hab : G.Reachable a b) :
    faceCount (G ⊔ edge a b) = faceCount G + 1 := by
  have hbound := card_le_edgeSet_add_components G
  have hedge := card_edgeSet_sup_edge G hne hadj
  have hcomp := card_components_sup_edge_of_reachable G a b hab
  unfold faceCount nullity
  rw [hedge, hcomp]
  omega


theorem faceCount_sup_edge_of_not_reachable (G : SimpleGraph V) {a b : V} (hne : a ≠ b)
    (hadj : ¬ G.Adj a b) (hab : ¬ G.Reachable a b) :
    faceCount (G ⊔ edge a b) = faceCount G := by
  have hbound := card_le_edgeSet_add_components G
  have hedge := card_edgeSet_sup_edge G hne hadj
  have hcomp := card_components_sup_edge_of_not_reachable G a b hab
  unfold faceCount nullity
  rw [hedge]
  omega


theorem euler_relation (G : SimpleGraph V) :
    Nat.card V + faceCount G = G.edgeSet.ncard + Nat.card G.ConnectedComponent + 1 := by
  have hbound := card_le_edgeSet_add_components G
  unfold faceCount nullity
  omega


theorem euler_relation_sub (G : SimpleGraph V) :
    (Nat.card V : ℤ) - G.edgeSet.ncard + faceCount G = Nat.card G.ConnectedComponent + 1 := by
  have h := euler_relation G
  have : (Nat.card V : ℤ) + (faceCount G : ℤ)
      = (G.edgeSet.ncard : ℤ) + (Nat.card G.ConnectedComponent : ℤ) + 1 := by exact_mod_cast h
  linarith


theorem card_components_eq_one_of_connected {G : SimpleGraph V} (hG : G.Connected) :
    Nat.card G.ConnectedComponent = 1 := by
  haveI : Nonempty V := hG.nonempty
  haveI := hG.preconnected.subsingleton_connectedComponent
  haveI : Nonempty G.ConnectedComponent := ⟨G.connectedComponentMk (Classical.arbitrary V)⟩
  rw [Nat.card_eq_one_iff_unique]
  exact ⟨inferInstance, inferInstance⟩


theorem euler_connected_nat {G : SimpleGraph V} (hG : G.Connected) :
    Nat.card V + faceCount G = G.edgeSet.ncard + 2 := by
  have h := euler_relation G
  rw [card_components_eq_one_of_connected hG] at h
  omega


theorem euler_connected {G : SimpleGraph V} (hG : G.Connected) :
    (Nat.card V : ℤ) - G.edgeSet.ncard + faceCount G = 2 := by
  have h := euler_relation_sub G
  rw [card_components_eq_one_of_connected hG] at h
  push_cast at h ⊢
  linarith


theorem nullity_eq_zero_of_isAcyclic {G : SimpleGraph V} (hG : G.IsAcyclic) :
    nullity G = 0 := by
  classical
  
  
  
  revert hG
  generalize hn : G.edgeSet.ncard = n
  induction n using Nat.strong_induction_on generalizing G with
  | _ n ih =>
    intro hG
    rcases Nat.eq_zero_or_pos n with hz | hpos
    · subst hz
      have hempty : G.edgeSet = ∅ := (Set.ncard_eq_zero (Set.toFinite G.edgeSet)).mp hn
      have hbot : G = ⊥ := by rw [← edgeSet_eq_empty]; exact hempty
      subst hbot
      unfold nullity
      rw [hn, card_components_bot]; simp
    · have hne : G.edgeSet.Nonempty := by
        rw [← Set.ncard_pos (Set.toFinite _), hn]; exact hpos
      obtain ⟨e, he⟩ := hne
      obtain ⟨a, b⟩ := e
      set G' := G.deleteEdges {s(a, b)} with hG'
      have hGeq : G = G' ⊔ edge a b := deleteEdges_sup_edge_eq G a b he
      have hdrop : G'.edgeSet.ncard + 1 = G.edgeSet.ncard :=
        card_edgeSet_deleteEdges_add_one G a b he
      have hn' : G'.edgeSet.ncard = n - 1 := by omega
      have hacyc' : G'.IsAcyclic := hG.anti (deleteEdges_le _)
      
      have hbridge : G.IsBridge s(a, b) := (isAcyclic_iff_forall_edge_isBridge.mp hG) he
      have hnr : ¬ G'.Reachable a b := isBridge_iff.mp hbridge
      have hne_ab : a ≠ b := G.ne_of_adj (by rwa [SimpleGraph.mem_edgeSet] at he)
      have hadj' : ¬ G'.Adj a b := by simp [hG', deleteEdges_adj]
      have ih' : nullity G' = 0 := ih (n - 1) (by omega) hn' hacyc'
      have hface : faceCount G = faceCount G' := by
        rw [hGeq]; exact faceCount_sup_edge_of_not_reachable G' hne_ab hadj' hnr
      unfold faceCount nullity at hface
      unfold nullity at ih' ⊢
      have hbound := card_le_edgeSet_add_components G
      have hbound' := card_le_edgeSet_add_components G'
      omega


theorem faceCount_eq_one_of_isAcyclic {G : SimpleGraph V} (hG : G.IsAcyclic) :
    faceCount G = 1 := by
  unfold faceCount; rw [nullity_eq_zero_of_isAcyclic hG]


theorem euler_tree {G : SimpleGraph V} (hG : G.IsTree) :
    (Nat.card V : ℤ) - G.edgeSet.ncard + faceCount G = 2 ∧ faceCount G = 1 := by
  refine ⟨euler_connected hG.connected, faceCount_eq_one_of_isAcyclic hG.isAcyclic⟩


theorem nullity_eq_cyclomaticNumber {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    (hG : G.Connected) :
    nullity G = cyclomaticNumber G := by
  unfold nullity cyclomaticNumber
  rw [card_components_eq_one_of_connected hG, Nat.card_eq_fintype_card]
  congr 1
  rw [Set.ncard_eq_toFinset_card', edgeFinset]


theorem faceCount_eq_cyclomaticNumber_add_one {G : SimpleGraph V} [Fintype V]
    [Fintype G.edgeSet] (hG : G.Connected) :
    faceCount G = cyclomaticNumber G + 1 := by
  unfold faceCount; rw [nullity_eq_cyclomaticNumber hG]


end StatMech.Lattice
