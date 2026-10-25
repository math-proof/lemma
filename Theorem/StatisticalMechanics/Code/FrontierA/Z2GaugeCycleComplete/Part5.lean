/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCycleComplete.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeWilsonAffine.Part3
import Theorem.StatisticalMechanics.Code.Ising.KWClosedWalkParity.Part14
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeCycleComplete.Part4
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


theorem cycleComplete_incidenceCount_eq [Nonempty V]
    (hG : G.Preconnected) (A : Finset G.edgeFinset)
    (q : CycleCompleteConstraint G) :
    plaquetteIncidenceCount (cycleCompleteIncidence G hG) A q =
      (A.filter (fun e =>
        e.1 ∈ walkOddSupport G (cycleCompleteWitnessWalk G hG q))).card := by
  rw [plaquetteIncidenceCount, card_filter]
  apply Finset.sum_congr rfl
  intro e he
  simp [cycleCompleteIncidence]


end
end StatMech.FrontierA
