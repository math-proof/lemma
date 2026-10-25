/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP2CoordinateReindex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackbonePartialP2Reindex.Part3
import Def.StatisticalMechanics.Code.Sharpness.BackboneP2CoordinateReindex
open SimpleGraph Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneP2CoordinateReindex

open BackboneLabeledSwitching

open BackbonePartialP2Reindex

variable {H G : SimpleGraph V}


omit [DecidableEq V] in

lemma edgeFinset_subset (hHG : H ≤ G) : H.edgeFinset ⊆ G.edgeFinset := by
  intro e he
  rw [SimpleGraph.mem_edgeFinset] at he ⊢
  exact edgeSet_mono hHG he


theorem extendFlux_injective (hHG : H ≤ G) :
    Function.Injective (extendFlux hHG) := by
  intro r t hrt
  funext e
  have heG : e.1 ∈ G.edgeFinset := edgeFinset_subset hHG e.2
  have heq := congrFun hrt (⟨e.1, heG⟩ : G.edgeFinset)
  simpa [extendFlux, e.2] using heq


theorem ofEdgeFun_extendFlux (hHG : H ≤ G) (r : H.edgeFinset -> Nat) :
    ofEdgeFun G (extendFlux hHG r) = ofEdgeFun H r := by
  funext e
  by_cases heH : e ∈ H.edgeFinset
  · have heG : e ∈ G.edgeFinset := edgeFinset_subset hHG heH
    simp [ofEdgeFun, extendFlux, heH, heG]
  · simp [ofEdgeFun, extendFlux, heH]


theorem incidentFlux_extendFlux (hHG : H ≤ G)
    (r : H.edgeFinset -> Nat) (x : V) :
    incidentFlux G (ofEdgeFun G (extendFlux hHG r)) x =
      incidentFlux H (ofEdgeFun H r) x := by
  rw [ofEdgeFun_extendFlux hHG r]
  unfold incidentFlux
  symm
  apply Finset.sum_subset
  · intro e he
    rw [Finset.mem_filter] at he ⊢
    exact ⟨edgeFinset_subset hHG he.1, he.2⟩
  · intro e heG heH
    rw [Finset.mem_filter] at heG
    have hnot : e ∉ H.edgeFinset := by
      intro he
      exact heH (by simp [he, heG.2])
    simp [ofEdgeFun, hnot]


theorem sources_extendFlux (hHG : H ≤ G) (r : H.edgeFinset -> Nat) :
    sources G (ofEdgeFun G (extendFlux hHG r)) =
      sources H (ofEdgeFun H r) := by
  ext x
  simp only [mem_sources]
  rw [incidentFlux_extendFlux hHG r x]


theorem weight_extendFlux (hHG : H ≤ G) (beta : Real)
    (J : Sym2 V -> Real) (r : H.edgeFinset -> Nat) :
    weight G beta J (ofEdgeFun G (extendFlux hHG r)) =
      weight H beta J (ofEdgeFun H r) := by
  rw [ofEdgeFun_extendFlux hHG r]
  unfold weight
  symm
  apply Finset.prod_subset (edgeFinset_subset hHG)
  intro e heG heH
  have hzero : ofEdgeFun H r e = 0 := by
    simp [ofEdgeFun, heH]
  simp [hzero]


end BackboneP2CoordinateReindex
end
end StatMech.Sharpness
