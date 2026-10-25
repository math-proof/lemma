/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneActualSelectorSwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneExplorationSelectorAdmissible.Part3
import Def.StatisticalMechanics.Code.Sharpness.BackboneActualSelectorSwitching.Part2
open SimpleGraph Finset
open scoped BigOperators

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

theorem shb_CurrentDynamicSelector.actualMass_eq_fiberTsum
    (S : shb_CurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V)
    (word : List (shb_ExplorationSegment V)) :
    S.actualMass beta J d word =
      ∑' m : d.graph.edgeFinset -> Nat,
        if S.Fiber d word m then weight d.graph beta J (ofEdgeFun d.graph m)
        else 0 := by
  unfold shb_CurrentDynamicSelector.actualMass
    shb_actualExplorationFiberMass shb_CurrentDynamicSelector.Fiber
  apply tsum_congr
  intro m
  by_cases h :
      sources d.graph (ofEdgeFun d.graph m) = S.sourceClass d word /\
        S.select d m = word <;> simp [h]


end
end StatMech.Sharpness
