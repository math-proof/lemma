/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc113boundaryforest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Walls.bc113boundaryforest.Part3
open Set SimpleGraph Finset

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option maxRecDepth 4000


namespace StatMech.Walls

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem bc113_bForest_adj (G : SimpleGraph V) (B : V → Prop) (hreach : bc113_ReachesB G B)
    {x y : V} :
    (bc113_bForest G B hreach).Adj x y ↔
      (∃ v, ¬ B v ∧ s(x, y) = s(v, bc113_parent G B hreach v)) ∧ x ≠ y := by
  classical
  simp only [bc113_bForest, SimpleGraph.fromEdgeSet_adj, Set.mem_setOf_eq]


theorem bc113_bForest_le (G : SimpleGraph V) (B : V → Prop) (hreach : bc113_ReachesB G B) :
    bc113_bForest G B hreach ≤ G := by
  classical
  intro x y hxy
  rw [bc113_bForest_adj] at hxy
  obtain ⟨⟨v, hvB, he⟩, hne⟩ := hxy
  rw [Sym2.eq_iff] at he
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact (bc113_parent_spec G B hreach hvB).1
  · exact (bc113_parent_spec G B hreach hvB).1.symm


theorem bc113_bForest_toB_ne (G : SimpleGraph V) (B : V → Prop) (hreach : bc113_ReachesB G B)
    {x y : V} (hxy : (bc113_bForest G B hreach).Adj x y) :
    bc113_toB G B x ≠ bc113_toB G B y := by
  classical
  rw [bc113_bForest_adj] at hxy
  obtain ⟨⟨v, hvB, he⟩, hne⟩ := hxy
  rw [Sym2.eq_iff] at he
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact fun h => absurd h (by have := (bc113_parent_spec G B hreach hvB).2; omega)
  · exact fun h => absurd h.symm (by have := (bc113_parent_spec G B hreach hvB).2; omega)


theorem bc113_bForest_down_is_parent (G : SimpleGraph V) (B : V → Prop) (hreach : bc113_ReachesB G B)
    {x y : V} (hxy : (bc113_bForest G B hreach).Adj x y)
    (hlt : bc113_toB G B y < bc113_toB G B x) :
    ¬ B x ∧ y = bc113_parent G B hreach x := by
  classical
  rw [bc113_bForest_adj] at hxy
  obtain ⟨⟨v, hvB, he⟩, hne⟩ := hxy
  rw [Sym2.eq_iff] at he
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · 
    exact ⟨hvB, rfl⟩
  · 
    exfalso
    have := (bc113_parent_spec G B hreach hvB).2
    omega


theorem bc113_bForest_down_unique (G : SimpleGraph V) (B : V → Prop) (hreach : bc113_ReachesB G B)
    {x y₁ y₂ : V} (h₁ : (bc113_bForest G B hreach).Adj x y₁)
    (h₂ : (bc113_bForest G B hreach).Adj x y₂)
    (hlt₁ : bc113_toB G B y₁ < bc113_toB G B x) (hlt₂ : bc113_toB G B y₂ < bc113_toB G B x) :
    y₁ = y₂ := by
  obtain ⟨_, he₁⟩ := bc113_bForest_down_is_parent G B hreach h₁ hlt₁
  obtain ⟨_, he₂⟩ := bc113_bForest_down_is_parent G B hreach h₂ hlt₂
  rw [he₁, he₂]


theorem bc113_bForest_adj_parent (G : SimpleGraph V) (B : V → Prop) (hreach : bc113_ReachesB G B)
    {v : V} (hv : ¬ B v) : (bc113_bForest G B hreach).Adj v (bc113_parent G B hreach v) := by
  classical
  rw [bc113_bForest_adj]
  refine ⟨⟨v, hv, rfl⟩, ?_⟩
  
  have hlt := (bc113_parent_spec G B hreach hv).2
  exact fun h => (Nat.ne_of_lt hlt) (congrArg (bc113_toB G B) h.symm)


theorem bc113_bForest_degree_pos_of_not_mem (G : SimpleGraph V) (B : V → Prop)
    (hreach : bc113_ReachesB G B) [DecidableRel (bc113_bForest G B hreach).Adj]
    {v : V} (hv : ¬ B v) : 1 ≤ (bc113_bForest G B hreach).degree v := by
  rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero,
    (bc113_bForest G B hreach).degree_pos_iff_exists_adj]
  exact ⟨_, bc113_bForest_adj_parent G B hreach hv⟩


theorem bc113_leaf_is_tip (G : SimpleGraph V) (B : V → Prop) (hreach : bc113_ReachesB G B)
    [DecidableRel (bc113_bForest G B hreach).Adj]
    {v : V} (hv : ¬ B v) (hdeg : (bc113_bForest G B hreach).degree v = 1) :
    ∀ u, (bc113_bForest G B hreach).Adj v u → u = bc113_parent G B hreach v := by
  classical
  intro u hu
  
  rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj] at hdeg
  obtain ⟨w, hw, huniq⟩ := hdeg
  have hpar := bc113_bForest_adj_parent G B hreach hv
  rw [huniq u hu, huniq _ hpar]


theorem bc113_bForest_acyclic (G : SimpleGraph V) (B : V → Prop) (hreach : bc113_ReachesB G B) :
    (bc113_bForest G B hreach).IsAcyclic := by
  classical
  set F := bc113_bForest G B hreach with hF
  set pot : V → ℕ := bc113_toB G B with hpot
  have hne : ∀ {x y : V}, F.Adj x y → pot x ≠ pot y := fun h => bc113_bForest_toB_ne G B hreach h
  have hunique : ∀ {x y₁ y₂ : V}, F.Adj x y₁ → F.Adj x y₂ →
      pot y₁ < pot x → pot y₂ < pot x → y₁ = y₂ :=
    fun h1 h2 l1 l2 => bc113_bForest_down_unique G B hreach h1 h2 l1 l2
  intro v c hc
  have hsupp_ne : c.support.toFinset.Nonempty := ⟨v, by simp⟩
  obtain ⟨m, hm_mem, hm_max⟩ := Finset.exists_max_image c.support.toFinset pot hsupp_ne
  rw [List.mem_toFinset] at hm_mem
  set d := c.rotate m hm_mem with hd
  have hcd : d.IsCycle := hc.rotate hm_mem
  have hdnn : ¬ d.Nil := hcd.not_nil
  have hadj_snd : F.Adj m d.snd := d.adj_snd hdnn
  have hadj_pen : F.Adj d.penultimate m := d.adj_penultimate hdnn
  have hadj_pen' : F.Adj m d.penultimate := hadj_pen.symm
  have hsupp_eq : d.support.toFinset = c.support.toFinset := by
    apply Finset.ext; intro x
    simp only [List.mem_toFinset]; rw [hd, SimpleGraph.Walk.mem_support_rotate_iff]
  have hsnd_supp : d.snd ∈ c.support := by
    have hmem : d.snd ∈ d.support := List.mem_of_mem_tail (d.snd_mem_tail_support hdnn)
    rw [← List.mem_toFinset, hsupp_eq, List.mem_toFinset] at hmem; exact hmem
  have hpen_supp : d.penultimate ∈ c.support := by
    have hmem : d.penultimate ∈ d.support := by
      have h2 : d.penultimate = d.reverse.snd := (SimpleGraph.Walk.snd_reverse d).symm
      rw [h2]
      have hrn : ¬ d.reverse.Nil := by
        rw [SimpleGraph.Walk.not_nil_iff_lt_length] at hdnn ⊢; simpa using hdnn
      have hmt : d.reverse.snd ∈ d.reverse.support :=
        List.mem_of_mem_tail (d.reverse.snd_mem_tail_support hrn)
      rw [SimpleGraph.Walk.support_reverse] at hmt; exact List.mem_reverse.mp hmt
    rw [← List.mem_toFinset, hsupp_eq, List.mem_toFinset] at hmem; exact hmem
  have hle_snd : pot d.snd ≤ pot m := hm_max _ (List.mem_toFinset.mpr hsnd_supp)
  have hle_pen : pot d.penultimate ≤ pot m := hm_max _ (List.mem_toFinset.mpr hpen_supp)
  have hlt_snd : pot d.snd < pot m := lt_of_le_of_ne hle_snd (fun h => (hne hadj_snd) h.symm)
  have hlt_pen : pot d.penultimate < pot m :=
    lt_of_le_of_ne hle_pen (fun h => (hne hadj_pen') h.symm)
  have heq : d.snd = d.penultimate := hunique hadj_snd hadj_pen' hlt_snd hlt_pen
  exact hcd.snd_ne_penultimate heq


end StatMech.Walls
