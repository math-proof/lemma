/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePartialEdgeCopySwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Sharpness.BackboneExplorationRealization.Part12
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.BackbonePartialEdgeCopySwitching.Part3
open SimpleGraph Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneLabeledSwitching

open FluxEdgeCopy

open RandomCurrent

variable (G : SimpleGraph V) [DecidableRel G.Adj]


def Fiber (m : G.edgeFinset -> Nat) (A : Finset V)
    (Q : Finset (FluxEdgeCopy.Copy G m) -> Prop) :=
  {S : Finset (FluxEdgeCopy.Copy G m) //
    RandomCurrent.sources (endsM G m) S = A ∧ Q S}

end BackboneLabeledSwitching
end
end StatMech.Sharpness
