/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneActualSelectorSwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneExplorationSelectorAdmissible.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneActualSelectorSwitching.Part2
open SimpleGraph Finset
open scoped BigOperators

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

abbrev shb_SelectorSwitchPair (d : shb_ExplorationDomain V)
    (s : shb_ExplorationSegment V) :=
  (d.graph.edgeFinset -> Nat) ×
    ((shb_BackboneExplorationDomain.advance d s).graph.edgeFinset -> Nat)


end
end StatMech.Sharpness
