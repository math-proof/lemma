/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneActualSelectorSwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneExplorationSelectorAdmissible.Part3
import Instance.StatisticalMechanics.Code.Sharpness.BackboneActualSelectorSwitching.Part2
open SimpleGraph Finset
open scoped BigOperators

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

noncomputable def shb_CurrentDynamicSelector.actualMass
    (S : shb_CurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real) : shb_ExplorationFiberMass V :=
  shb_actualExplorationFiberMass beta J S.sourceClass
    (fun d word m => S.select d m = word)


end
end StatMech.Sharpness
