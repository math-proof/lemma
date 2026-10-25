/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePartialEdgeCopySwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Sharpness.BackboneExplorationRealization.Part12
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Instance.StatisticalMechanics.Code.Sharpness.BackbonePartialEdgeCopySwitching.Part3
open SimpleGraph Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

noncomputable def shb_oneStepChosenSegment
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat) :
    Option (shb_ExplorationSegment V) :=
  if h : ∃ s, shb_oneStepCandidate d m s then some (Classical.choose h)
  else none

end
end StatMech.Sharpness
