/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneActualSelectorObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneActualSelectorSwitching.Part3
import Def.StatisticalMechanics.Code.Sharpness.BackboneActualSelectorObstruction.Part2
open SimpleGraph Finset

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

theorem shb_singleEdgeFlux_incidentFlux_left {x y : V} (hxy : x ≠ y) :
    incidentFlux (shb_emptyActiveSingleEdgeDomain x y).graph
        (ofEdgeFun (shb_emptyActiveSingleEdgeDomain x y).graph
          (shb_singleEdgeFlux x y)) x = 1 := by
  unfold incidentFlux
  rw [show (shb_emptyActiveSingleEdgeDomain x y).graph.edgeFinset =
      {s(x, y)} by exact shb_singleEdgeGraph_edgeFinset hxy]
  have hfilter : ({s(x, y)} : Finset (Sym2 V)).filter (fun e => x ∈ e) =
      {s(x, y)} := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · exact And.left
    · intro he
      subst e
      exact ⟨rfl, Sym2.mem_mk_left x y⟩
  rw [hfilter, Finset.sum_singleton]
  unfold ofEdgeFun shb_singleEdgeFlux
  rw [dif_pos]
  exact shb_singleEdgeGraph_edge_mem hxy


theorem shb_singleEdgeFlux_sources_ne_empty {x y : V} (hxy : x ≠ y) :
    sources (shb_emptyActiveSingleEdgeDomain x y).graph
        (ofEdgeFun (shb_emptyActiveSingleEdgeDomain x y).graph
          (shb_singleEdgeFlux x y)) ≠ ∅ := by
  intro hs
  have hx : x ∈ sources (shb_emptyActiveSingleEdgeDomain x y).graph
      (ofEdgeFun (shb_emptyActiveSingleEdgeDomain x y).graph
        (shb_singleEdgeFlux x y)) := by
    rw [mem_sources, shb_singleEdgeFlux_incidentFlux_left hxy]
    exact odd_one
  rw [hs] at hx
  simp at hx


theorem shb_CurrentDynamicSelector_isEmpty_of_exists_ne
    (hne : ∃ x : V, ∃ y : V, x ≠ y) :
    IsEmpty (shb_CurrentDynamicSelector (V := V)) := by
  constructor
  intro S
  obtain ⟨x, y, hxy⟩ := hne
  let d := shb_emptyActiveSingleEdgeDomain x y
  let m := shb_singleEdgeFlux x y
  cases hword : S.select d m with
  | nil =>
      have hs := S.sources_eq_sourceClass_of_select d m [] hword
      rw [S.sourceClass_nil d] at hs
      exact shb_singleEdgeFlux_sources_ne_empty hxy hs
  | cons s ss =>
      have hsInactive : s ∉ d.active := by simp [d, shb_emptyActiveSingleEdgeDomain]
      exact S.select_ne_cons_of_not_active d s ss m hsInactive hword


theorem shb_no_CurrentDynamicSelector_bool :
    IsEmpty (shb_CurrentDynamicSelector (V := Bool)) := by
  apply shb_CurrentDynamicSelector_isEmpty_of_exists_ne
  exact ⟨false, true, by decide⟩


end
end StatMech.Sharpness
