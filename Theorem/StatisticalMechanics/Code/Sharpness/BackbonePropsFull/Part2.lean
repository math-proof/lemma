/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePropsFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part10
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneProps.Part2
import Theorem.StatisticalMechanics.Code.Ising.TwoReplica.Part7
import Def.StatisticalMechanics.Code.Sharpness.BackbonePropsFull.Part3
open SimpleGraph Finset
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech

namespace Sharpness

open StatMech.Ising (bond)

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem shb_adjP_oddEdges_imp_adj (n : Current V) {a b : V}
    (h : StatMech.Ising.adjP (StatMech.Ising.oddEdges G.edgeFinset n) a b) :
    (oddSubgraph G n).Adj a b := by
  obtain ⟨e, he, ha, hb, hne⟩ := h
  rw [StatMech.Ising.oddEdges, Finset.mem_filter, SimpleGraph.mem_edgeFinset] at he
  obtain ⟨heG, hodd⟩ := he
  have hee : e = s(a, b) := (Sym2.mem_and_mem_iff hne).mp ⟨ha, hb⟩
  rw [hee, SimpleGraph.mem_edgeSet] at heG
  rw [hee] at hodd
  exact ⟨heG, hodd⟩


theorem shb_connP_oddEdges_imp_reachable (n : Current V) {a b : V}
    (h : StatMech.Ising.connP (StatMech.Ising.oddEdges G.edgeFinset n) a b) :
    (oddSubgraph G n).Reachable a b := by
  induction h with
  | refl => exact SimpleGraph.Reachable.refl _
  | tail _ hstep ih => exact ih.trans (shb_adjP_oddEdges_imp_adj G n hstep).reachable


theorem shb_sources_eq (n : Current V) :
    Sharpness.sources G n = StatMech.Ising.sources G.edgeFinset n := rfl


theorem shb_backbone_exists (n : Current V) {x y : V} (hxy : x ≠ y)
    (hsrc : Sharpness.sources G n = {x, y}) :
    Nonempty (IsBackbonePath G n x y) := by
  have hnd : ∀ e ∈ G.edgeFinset, ¬ e.IsDiag := by
    intro e he
    rw [SimpleGraph.mem_edgeFinset] at he
    exact SimpleGraph.not_isDiag_of_mem_edgeSet G he
  have hsrc' : StatMech.Ising.sources G.edgeFinset n = {x, y} := by
    rw [← shb_sources_eq]; exact hsrc
  have hconn := StatMech.Ising.connOdd_of_sources G.edgeFinset n hnd hxy hsrc'
  exact (shb_connP_oddEdges_imp_reachable G n hconn).elim (fun w => ⟨w.toPath⟩)


theorem shb_backboneSet_nonempty_of_sources (n : Current V) {x y : V} (hxy : x ≠ y)
    (hsrc : Sharpness.sources G n = {x, y}) :
    (shb_backboneSet G n x y).Nonempty :=
  ⟨_, shb_isBackbonePath_mem_backboneSet G n x y (shb_backbone_exists G n hxy hsrc).some⟩


end Sharpness
end StatMech
