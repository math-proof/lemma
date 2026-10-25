/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCycleComplete.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeWilsonAffine.Part3
import Theorem.StatisticalMechanics.Code.Ising.KWClosedWalkParity.Part14
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeCycleComplete.Part5
open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


theorem cycleCompleteEdgeSet_subset (A : Finset G.edgeFinset) :
    cycleCompleteEdgeSet G A ⊆ G.edgeFinset := by
  intro e he
  rw [cycleCompleteEdgeSet, Finset.mem_map] at he
  obtain ⟨p, _, rfl⟩ := he
  exact p.2

theorem cycleComplete_incidence_even_iff_walkParity [Nonempty V]
    (hG : G.Preconnected) (A : Finset G.edgeFinset)
    (q : CycleCompleteConstraint G) :
    Even (plaquetteIncidenceCount (cycleCompleteIncidence G hG) A q) ↔
      walkParity G (cycleCompleteEdgeSet G A)
        (cycleCompleteWitnessWalk G hG q) = false := by
  rw [cycleComplete_incidenceCount_eq]
  rw [← even_filter_walkOddSupport_iff_walkParity_false G
    (cycleCompleteEdgeSet G A) (cycleCompleteWitnessWalk G hG q)]
  apply iff_of_eq
  congr 1
  rw [cycleCompleteEdgeSet, Finset.filter_map, Finset.card_map]
  rfl


theorem cycleComplete_isClosed_iff_mem_cutSpace [Nonempty V]
    (hG : G.Preconnected) (A : Finset G.edgeFinset) :
    IsClosedPlaquetteSet (cycleCompleteIncidence G hG) A ↔
      cycleCompleteEdgeSet G A ∈ cutSpace G := by
  constructor
  · intro hclosed
    by_contra hnot
    let q : CycleCompleteConstraint G :=
      ⟨cycleCompleteEdgeSet G A, cycleCompleteEdgeSet_subset G A, hnot⟩
    have heven := hclosed q
    have hfalse : walkParity G (cycleCompleteEdgeSet G A)
        (cycleCompleteWitnessWalk G hG q) = false :=
      (cycleComplete_incidence_even_iff_walkParity G hG A q).mp heven
    have htrue := cycleCompleteWitnessWalk_odd G hG q
    rw [htrue] at hfalse
    simp at hfalse
  · intro hcut q
    apply (cycleComplete_incidence_even_iff_walkParity G hG A q).mpr
    exact evenOnCycles_of_mem_cutSpace hcut _ _


end
end StatMech.FrontierA
