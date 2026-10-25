/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempKacWard.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopLowTempDual.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardArbitraryValenceClosure
import Def.StatisticalMechanics.Code.Onsager.SignedLoopLowTempKacWard
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice

open StatMech.FrontierA

noncomputable section

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E]

@[simp] theorem kwg_subdivCentralEdge_injective :
    Function.Injective (kwg_subdivCentralEdge : E -> kwg_SubdivEdge V E) := by
  intro e e' h
  unfold kwg_subdivCentralEdge at h
  rw [Sym2.eq_iff] at h
  rcases h with h | h <;> simp only [Sum.inr.injEq, Prod.mk.injEq,
    Bool.false_eq_true, Bool.true_eq_false, and_false] at h
  exact h.1.1

@[simp] theorem kwg_subdivCentralEdge_mem_gadget (ends : E -> Sym2 V)
    (e e' : E) :
    kwg_subdivCentralEdge e' ∈ kwg_subdivGadgetEdges ends e ↔ e' = e := by
  simp only [kwg_subdivGadgetEdges, Finset.mem_insert, Finset.mem_singleton]
  unfold kwg_subdivCentralEdge kwg_subdivLeftEdge kwg_subdivRightEdge
  rw [Sym2.eq_iff, Sym2.eq_iff, Sym2.eq_iff]
  simp

@[simp] theorem kwg_subdivCentralEdge_mem_lift (ends : E -> Sym2 V)
    (F : Finset E) (e : E) :
    kwg_subdivCentralEdge e ∈ kwg_subdivLift ends F ↔ e ∈ F := by
  simp [kwg_subdivLift]


theorem kwg_subdivGraph_mem_edgeFinset_iff (ends : E -> Sym2 V)
    (edge : kwg_SubdivEdge V E) :
    edge ∈ (kwg_subdivGraph ends).edgeFinset ↔
      ∃ e : E, edge ∈ kwg_subdivGadgetEdges ends e := by
  induction edge using Sym2.inductionOn with
  | _ a b =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      rcases a with v | ⟨e, c⟩ <;> rcases b with w | ⟨e', c'⟩
      · simp only [kwg_subdivGraph, false_iff, not_exists]
        intro e
        simp [kwg_subdivGadgetEdges, kwg_subdivLeftEdge,
          kwg_subdivCentralEdge, kwg_subdivRightEdge, Sym2.eq_iff]
      · cases c' <;>
          simp [kwg_subdivGraph, kwg_subdivGadgetEdges,
            kwg_subdivLeftEdge, kwg_subdivCentralEdge,
            kwg_subdivRightEdge, Sym2.eq_iff]
      · cases c <;>
          simp [kwg_subdivGraph, kwg_subdivGadgetEdges,
            kwg_subdivLeftEdge, kwg_subdivCentralEdge,
            kwg_subdivRightEdge, Sym2.eq_iff, eq_comm]
      · cases c <;> cases c' <;>
          simp [kwg_subdivGraph, kwg_subdivGadgetEdges,
            kwg_subdivLeftEdge, kwg_subdivCentralEdge,
            kwg_subdivRightEdge, Sym2.eq_iff, eq_comm]

theorem kwg_subdivLift_subset_edgeFinset (ends : E -> Sym2 V)
    (F : Finset E) :
    kwg_subdivLift ends F ⊆ (kwg_subdivGraph ends).edgeFinset := by
  intro edge hedge
  rw [kwg_subdivGraph_mem_edgeFinset_iff]
  unfold kwg_subdivLift at hedge
  rw [Finset.mem_biUnion] at hedge
  exact ⟨hedge.choose, hedge.choose_spec.2⟩

@[simp] theorem kwg_subdivGraph_neighborFinset_false
    (ends : E -> Sym2 V) (e : E) :
    (kwg_subdivGraph ends).neighborFinset (Sum.inr (e, false)) =
      {Sum.inl (ends e).out.1, Sum.inr (e, true)} := by
  ext z
  rw [SimpleGraph.mem_neighborFinset]
  rcases z with v | ⟨e', b⟩
  · simp [kwg_subdivGraph, eq_comm]
  · cases b <;> simp [kwg_subdivGraph, eq_comm]

@[simp] theorem kwg_subdivGraph_neighborFinset_true
    (ends : E -> Sym2 V) (e : E) :
    (kwg_subdivGraph ends).neighborFinset (Sum.inr (e, true)) =
      {Sum.inr (e, false), Sum.inl (ends e).out.2} := by
  ext z
  rw [SimpleGraph.mem_neighborFinset]
  rcases z with v | ⟨e', b⟩
  · simp [kwg_subdivGraph, eq_comm]
  · cases b <;> simp [kwg_subdivGraph, eq_comm]


theorem kwg_evenSubgraph_gadget_membership (ends : E -> Sym2 V)
    (H : Finset (kwg_SubdivEdge V E))
    (hH : H ∈ evenSubgraphs (kwg_subdivGraph ends)) (e : E) :
    kwg_subdivLeftEdge ends e ∈ H ↔ kwg_subdivCentralEdge e ∈ H := by
  letI : SimpleGraph.LocallyFinite (kwg_subdivGraph ends) :=
    fun _ => Subtype.fintype _
  have hsum := kw_evenSubgraph_neighbor_sum_zero
    (kwg_subdivGraph ends) H hH (Sum.inr (e, false))
  have hsum' :
      (∑ w ∈ ({Sum.inl (ends e).out.1, Sum.inr (e, true)} :
          Finset (kwg_SubdivVertex V E)),
        if s(Sum.inr (e, false), w) ∈ H then (1 : ZMod 2) else 0) = 0 := by
    calc
      _ = ∑ w ∈ (kwg_subdivGraph ends).neighborFinset
          (Sum.inr (e, false)),
          if s(Sum.inr (e, false), w) ∈ H then (1 : ZMod 2) else 0 := by
        apply Finset.sum_congr
        · ext z
          rw [SimpleGraph.mem_neighborFinset]
          rcases z with v | ⟨e', b⟩
          · simp [kwg_subdivGraph, eq_comm]
          · cases b <;> simp [kwg_subdivGraph, eq_comm]
        · intros
          rfl
      _ = 0 := hsum
  have hparity :
      (if kwg_subdivLeftEdge ends e ∈ H then (1 : ZMod 2) else 0) +
        (if kwg_subdivCentralEdge e ∈ H then 1 else 0) = 0 := by
    rw [Finset.sum_insert (by simp), Finset.sum_singleton] at hsum'
    simpa only [kwg_subdivLeftEdge, kwg_subdivCentralEdge,
      Sym2.eq_swap] using hsum'
  by_cases hl : kwg_subdivLeftEdge ends e ∈ H <;>
    by_cases hc : kwg_subdivCentralEdge e ∈ H <;> simp [hl, hc] at hparity ⊢

theorem kwg_evenSubgraph_gadget_membership_right (ends : E -> Sym2 V)
    (H : Finset (kwg_SubdivEdge V E))
    (hH : H ∈ evenSubgraphs (kwg_subdivGraph ends)) (e : E) :
    kwg_subdivRightEdge ends e ∈ H ↔ kwg_subdivCentralEdge e ∈ H := by
  letI : SimpleGraph.LocallyFinite (kwg_subdivGraph ends) :=
    fun _ => Subtype.fintype _
  have hsum := kw_evenSubgraph_neighbor_sum_zero
    (kwg_subdivGraph ends) H hH (Sum.inr (e, true))
  have hsum' :
      (∑ w ∈ ({Sum.inr (e, false), Sum.inl (ends e).out.2} :
          Finset (kwg_SubdivVertex V E)),
        if s(Sum.inr (e, true), w) ∈ H then (1 : ZMod 2) else 0) = 0 := by
    calc
      _ = ∑ w ∈ (kwg_subdivGraph ends).neighborFinset
          (Sum.inr (e, true)),
          if s(Sum.inr (e, true), w) ∈ H then (1 : ZMod 2) else 0 := by
        apply Finset.sum_congr
        · ext z
          rw [SimpleGraph.mem_neighborFinset]
          rcases z with v | ⟨e', b⟩
          · simp [kwg_subdivGraph, eq_comm]
          · cases b <;> simp [kwg_subdivGraph, eq_comm]
        · intros
          rfl
      _ = 0 := hsum
  have hparity :
      (if kwg_subdivCentralEdge e ∈ H then (1 : ZMod 2) else 0) +
        (if kwg_subdivRightEdge ends e ∈ H then 1 else 0) = 0 := by
    rw [Finset.sum_insert (by simp), Finset.sum_singleton] at hsum'
    simpa only [kwg_subdivCentralEdge, kwg_subdivRightEdge,
      Sym2.eq_swap] using hsum'
  by_cases hr : kwg_subdivRightEdge ends e ∈ H <;>
    by_cases hc : kwg_subdivCentralEdge e ∈ H <;> simp [hr, hc] at hparity ⊢


end
end StatMech.Onsager
