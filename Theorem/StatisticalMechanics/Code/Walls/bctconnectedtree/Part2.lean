/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bctconnectedtree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bgeexploration.Part2
import Def.StatisticalMechanics.Code.Walls.bctconnectedtree.Part2
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


theorem bct_walk_fst_const {β V : Type} {H : SimpleGraph V} {p q : β × V}
    (w : (bct_fiberForest β V H).Walk p q) : ∀ v ∈ w.support, v.1 = p.1 := by
  induction w with
  | nil => intro v hv; simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hv; rw [hv]
  | @cons a b c hadj w' ih =>
    intro v hv
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
    rcases hv with rfl | hv
    · rfl
    · rw [ih v hv]; exact (bct_fiberForest_fst hadj).symm


theorem bct_snd_injOn_support {β V : Type} {H : SimpleGraph V} {v : β × V}
    (c : (bct_fiberForest β V H).Walk v v) :
    Set.InjOn (Prod.snd : β × V → V) {x | x ∈ c.support} := by
  intro a ha b hb hab
  exact Prod.ext ((bct_walk_fst_const c a ha).trans (bct_walk_fst_const c b hb).symm) hab


theorem bct_fiberForest_acyclic (β V : Type) (H : SimpleGraph V) (hH : H.IsAcyclic) :
    (bct_fiberForest β V H).IsAcyclic := by
  intro v c hc
  have hinj := bct_snd_injOn_support c
  have hcm : (c.map (bct_sndHom β V H)).IsCycle := by
    rw [SimpleGraph.Walk.isCycle_def] at hc ⊢
    obtain ⟨htr, hne, hnodup⟩ := hc
    refine ⟨?_, ?_, ?_⟩
    · rw [SimpleGraph.Walk.isTrail_def] at htr ⊢
      rw [SimpleGraph.Walk.edges_map]
      apply List.Nodup.map_on _ htr
      intro e1 he1 e2 he2 hee
      induction e1 using Sym2.ind with | _ a1 b1 =>
      induction e2 using Sym2.ind with | _ a2 b2 =>
      simp only [Sym2.map_mk] at hee
      have ha1 : a1 ∈ c.support := c.fst_mem_support_of_mem_edges he1
      have hb1 : b1 ∈ c.support := c.snd_mem_support_of_mem_edges he1
      have ha2 : a2 ∈ c.support := c.fst_mem_support_of_mem_edges he2
      have hb2 : b2 ∈ c.support := c.snd_mem_support_of_mem_edges he2
      rw [Sym2.eq_iff] at hee ⊢
      rcases hee with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · left; exact ⟨hinj ha1 ha2 e1, hinj hb1 hb2 e2⟩
      · right; exact ⟨hinj ha1 hb2 e1, hinj hb1 ha2 e2⟩
    · intro h
      apply hne
      cases c with
      | nil => rfl
      | cons hh w => simp [SimpleGraph.Walk.map_cons] at h
    · rw [SimpleGraph.Walk.support_map, ← List.map_tail]
      apply List.Nodup.map_on _ hnodup
      intro x hx y hy hxy
      exact hinj (List.mem_of_mem_tail hx) (List.mem_of_mem_tail hy) hxy
  exact hH (c.map (bct_sndHom β V H)) hcm


theorem bct_fiberForest_neighborFinset {β V : Type} [DecidableEq β] [Fintype β] [DecidableEq V]
    [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj] (t : β) (i : V) :
    (bct_fiberForest β V H).neighborFinset (t, i) = ({t} : Finset β) ×ˢ (H.neighborFinset i) := by
  classical
  ext ⟨t', j⟩
  simp only [SimpleGraph.mem_neighborFinset, bct_fiberForest_adj_iff, Finset.mem_product,
    Finset.mem_singleton]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1.symm, h2⟩, fun ⟨h1, h2⟩ => ⟨h1.symm, h2⟩⟩


theorem bct_fiberForest_degree {β V : Type} [DecidableEq β] [Fintype β] [DecidableEq V] [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (t : β) (i : V) :
    (bct_fiberForest β V H).degree (t, i) = H.degree i := by
  classical
  rw [SimpleGraph.degree, bct_fiberForest_neighborFinset, Finset.card_product,
    Finset.card_singleton, one_mul, SimpleGraph.degree]


end StatMech.Walls
