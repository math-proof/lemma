/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc113boundaryforest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Walls.bc113boundaryforest.Part5
open Set SimpleGraph Finset

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option maxRecDepth 4000


namespace StatMech.Walls

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem bc113_bForest_degree_pos_of_mem (G : SimpleGraph V) (B : V → Prop)
    (hreach : bc113_ReachesB G B) [DecidableRel (bc113_bForest G B hreach).Adj]
    (hbc : bc113_BoundaryHasChild G B hreach) {b : V} (hb : B b) :
    1 ≤ (bc113_bForest G B hreach).degree b := by
  rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero,
    (bc113_bForest G B hreach).degree_pos_iff_exists_adj]
  exact hbc b hb


theorem bc113_bForest_min_degree (G : SimpleGraph V) (B : V → Prop) (hreach : bc113_ReachesB G B)
    [DecidableRel (bc113_bForest G B hreach).Adj] (hbc : bc113_BoundaryHasChild G B hreach)
    (v : V) : 1 ≤ (bc113_bForest G B hreach).degree v := by
  by_cases hv : B v
  · exact bc113_bForest_degree_pos_of_mem G B hreach hbc hv
  · exact bc113_bForest_degree_pos_of_not_mem G B hreach hv


theorem bc113_boundaryAnchored_forest_exists (G : SimpleGraph V) (B : V → Prop)
    (hreach : bc113_ReachesB G B)
    (hchild : bc113_HasChild G B hreach) (hbc : bc113_BoundaryHasChild G B hreach) :
    ∃ (F : SimpleGraph V) (_ : DecidableRel F.Adj),
      F ≤ G ∧ F.IsAcyclic ∧ (∀ v, 1 ≤ F.degree v) ∧
      (∀ v, F.degree v = 1 → B v) := by
  classical
  refine ⟨bc113_bForest G B hreach, Classical.decRel _, bc113_bForest_le G B hreach,
    bc113_bForest_acyclic G B hreach, ?_, ?_⟩
  · intro v; exact bc113_bForest_min_degree G B hreach hbc v
  · intro v hdeg; exact bc113_bForest_leaves_on_boundary G B hreach hchild hdeg


theorem bc113_maxPotential_has_no_child (G : SimpleGraph V) (B : V → Prop)
    (hreach : bc113_ReachesB G B) {v : V} (hv : ¬ B v)
    (hmax : ∀ w, bc113_toB G B w ≤ bc113_toB G B v) :
    ¬ ∃ w, (bc113_bForest G B hreach).Adj v w ∧ bc113_toB G B v < bc113_toB G B w := by
  rintro ⟨w, _, hlt⟩
  exact absurd (hmax w) (by omega)


theorem bc113_no_boundaryAnchored_on_triangle :
    ¬ ∃ (F : SimpleGraph (Fin 3)) (_ : DecidableRel F.Adj),
        F ≤ (⊤ : SimpleGraph (Fin 3)) ∧ F.IsAcyclic ∧ (∀ v, 1 ≤ F.degree v) ∧
        (∀ v, F.degree v = 1 → v = 0) := by
  classical
  rintro ⟨F, hFdec, _hle, hac, hmin, hleaf⟩
  
  have hdeg_le : ∀ v : Fin 3, F.degree v ≤ 2 := by
    intro v
    have hb : F.degree v ≤ (⊤ : SimpleGraph (Fin 3)).degree v := by
      
      rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
      apply Finset.card_le_card
      intro w hw
      rw [SimpleGraph.mem_neighborFinset] at hw ⊢
      exact _hle hw
    have htop : (⊤ : SimpleGraph (Fin 3)).degree v = 2 := by fin_cases v <;> decide
    omega
  have hne1 : F.degree 1 ≠ 1 := fun h => absurd (hleaf 1 h) (by decide)
  have hne2 : F.degree 2 ≠ 1 := fun h => absurd (hleaf 2 h) (by decide)
  have hd1 : F.degree 1 = 2 := by have := hmin 1; have := hdeg_le 1; omega
  have hd2 : F.degree 2 = 2 := by have := hmin 2; have := hdeg_le 2; omega
  
  have hadj12 : F.Adj 1 2 := by
    by_contra hn
    
    have hsub : F.neighborFinset 1 ⊆ {0} := by
      intro w hw
      rw [SimpleGraph.mem_neighborFinset] at hw
      fin_cases w
      · simp
      · exact absurd hw F.irrefl
      · exact absurd hw hn
    have := Finset.card_le_card hsub
    rw [SimpleGraph.card_neighborFinset_eq_degree, hd1] at this
    simp at this
  have hadj10 : F.Adj 1 0 := by
    by_contra hn
    have hsub : F.neighborFinset 1 ⊆ {2} := by
      intro w hw
      rw [SimpleGraph.mem_neighborFinset] at hw
      fin_cases w
      · exact absurd hw hn
      · exact absurd hw F.irrefl
      · simp
    have := Finset.card_le_card hsub
    rw [SimpleGraph.card_neighborFinset_eq_degree, hd1] at this
    simp at this
  have hadj20 : F.Adj 2 0 := by
    by_contra hn
    have hsub : F.neighborFinset 2 ⊆ {1} := by
      intro w hw
      rw [SimpleGraph.mem_neighborFinset] at hw
      fin_cases w
      · exact absurd hw hn
      · simp
      · exact absurd hw F.irrefl
    have := Finset.card_le_card hsub
    rw [SimpleGraph.card_neighborFinset_eq_degree, hd2] at this
    simp at this
  
  set w : F.Walk 0 0 := SimpleGraph.Walk.cons hadj10.symm
      (SimpleGraph.Walk.cons hadj12 (SimpleGraph.Walk.cons hadj20 SimpleGraph.Walk.nil)) with hw
  refine hac w ?_
  rw [SimpleGraph.Walk.isCycle_def]
  refine ⟨?_, ?_, ?_⟩
  · 
    rw [SimpleGraph.Walk.isTrail_def, hw]
    simp only [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil]
    decide
  · 
    rw [hw]; exact fun h => (SimpleGraph.Walk.not_nil_cons) (h ▸ SimpleGraph.Walk.nil_nil)
  · 
    rw [hw]
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.tail_cons]
    decide


theorem bc113_boundaryAnchored_nonvacuous :
    ∃ (F : SimpleGraph (Fin 2)) (_ : DecidableRel F.Adj),
      F ≤ (⊤ : SimpleGraph (Fin 2)) ∧ F.IsAcyclic ∧ (∀ v, 1 ≤ F.degree v) ∧
      (∀ v, F.degree v = 1 → (fun _ : Fin 2 => True) v) := by
  classical
  refine ⟨SimpleGraph.fromEdgeSet {s((0 : Fin 2), 1)}, inferInstance, ?_, ?_, ?_, ?_⟩
  · intro x y hxy; rw [SimpleGraph.top_adj]
    exact (SimpleGraph.fromEdgeSet {s((0 : Fin 2), 1)}).ne_of_adj hxy
  · 
    rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge]
    intro u v huv
    rw [SimpleGraph.fromEdgeSet_adj] at huv
    obtain ⟨hmem, hne⟩ := huv
    simp only [Set.mem_singleton_iff, Sym2.eq_iff] at hmem
    rw [SimpleGraph.isBridge_iff]
    intro hreach
    obtain ⟨wlk⟩ := hreach
    have hbot : ((SimpleGraph.fromEdgeSet {s((0 : Fin 2), 1)}).deleteEdges {s(u, v)}) = ⊥ := by
      ext p q
      rw [SimpleGraph.deleteEdges_adj]
      simp only [SimpleGraph.fromEdgeSet_adj, Set.mem_singleton_iff, Sym2.eq_iff, SimpleGraph.bot_adj,
        iff_false, not_and]
      rintro ⟨hpq, hpqne⟩ hnpq
      apply hnpq
      rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hpq with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
        subst_vars <;> tauto
    rw [hbot] at wlk
    exact hne (wlk.eq_of_length_eq_zero
      (by cases wlk with | nil => rfl | cons h _ => exact absurd h (by simp)))
  · intro v
    
    rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero,
      (SimpleGraph.fromEdgeSet {s((0 : Fin 2), 1)}).degree_pos_iff_exists_adj]
    fin_cases v
    · exact ⟨1, by rw [SimpleGraph.fromEdgeSet_adj]; exact ⟨by simp, by decide⟩⟩
    · exact ⟨0, by rw [SimpleGraph.fromEdgeSet_adj]
                   refine ⟨by simp, by decide⟩⟩
  · intro v _; trivial


theorem bc113_hub_degree_ge_three (G : SimpleGraph V) (B : V → Prop) (hreach : bc113_ReachesB G B)
    [DecidableRel (bc113_bForest G B hreach).Adj] {v w₁ w₂ : V} (hv : ¬ B v)
    (ha₁ : (bc113_bForest G B hreach).Adj v w₁) (ha₂ : (bc113_bForest G B hreach).Adj v w₂)
    (hlt₁ : bc113_toB G B v < bc113_toB G B w₁) (hlt₂ : bc113_toB G B v < bc113_toB G B w₂)
    (hne : w₁ ≠ w₂) :
    3 ≤ (bc113_bForest G B hreach).degree v := by
  classical
  have hpar := bc113_bForest_adj_parent G B hreach hv
  have hparlt := (bc113_parent_spec G B hreach hv).2
  set p := bc113_parent G B hreach v with hp
  
  have hpw₁ : p ≠ w₁ := by intro h; rw [h] at hparlt; omega
  have hpw₂ : p ≠ w₂ := by intro h; rw [h] at hparlt; omega
  have hsub : {p, w₁, w₂} ⊆ (bc113_bForest G B hreach).neighborFinset v := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rw [SimpleGraph.mem_neighborFinset]
    rcases hz with rfl | rfl | rfl
    · exact hpar
    · exact ha₁
    · exact ha₂
  have hcard : ({p, w₁, w₂} : Finset V).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hne]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hpw₁, hpw₂⟩
  calc 3 = ({p, w₁, w₂} : Finset V).card := hcard.symm
    _ ≤ ((bc113_bForest G B hreach).neighborFinset v).card := Finset.card_le_card hsub
    _ = (bc113_bForest G B hreach).degree v := SimpleGraph.card_neighborFinset_eq_degree _ _


theorem bc113_status :
    
    (∀ (G : SimpleGraph V) (B : V → Prop) (hreach : bc113_ReachesB G B),
      (bc113_bForest G B hreach) ≤ G ∧ (bc113_bForest G B hreach).IsAcyclic) ∧
    
    (∀ (G : SimpleGraph V) (B : V → Prop) (hreach : bc113_ReachesB G B),
      bc113_HasChild G B hreach → bc113_BoundaryHasChild G B hreach →
      ∃ (F : SimpleGraph V) (_ : DecidableRel F.Adj),
        F ≤ G ∧ F.IsAcyclic ∧ (∀ v, 1 ≤ F.degree v) ∧ (∀ v, F.degree v = 1 → B v)) ∧
    
    (¬ ∃ (F : SimpleGraph (Fin 3)) (_ : DecidableRel F.Adj),
        F ≤ (⊤ : SimpleGraph (Fin 3)) ∧ F.IsAcyclic ∧ (∀ v, 1 ≤ F.degree v) ∧
        (∀ v, F.degree v = 1 → v = 0)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro G B hreach
    exact ⟨bc113_bForest_le G B hreach, bc113_bForest_acyclic G B hreach⟩
  · intro G B hreach hchild hbc
    exact bc113_boundaryAnchored_forest_exists G B hreach hchild hbc
  · exact bc113_no_boundaryAnchored_on_triangle

end StatMech.Walls
