/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneActualSelectorObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneActualSelectorSwitching.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneActualSelectorObstruction.Part2
open SimpleGraph Finset

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

def shb_singleEdgeConstantFlux (x y : V) (k : Nat) :
    (shb_singleEdgeGraph x y).edgeFinset -> Nat := fun _ => k


end
end StatMech.Sharpness
