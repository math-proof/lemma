/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondProgram.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneConcreteBondProgram.Part9
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeBondProgram.Part4
open SimpleGraph Finset
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneTwoEdgeBondProgram

open BackboneConcreteSelector

open BackboneConcreteBondProgram

open BackboneDeterminedCutSwitching

def twoUnitFlux (G : SimpleGraph V) (e f : G.edgeFinset) :
    G.edgeFinset -> Nat := fun g =>
  BackboneConcreteBondProgram.unitFlux G e g +
    BackboneConcreteBondProgram.unitFlux G f g


end BackboneTwoEdgeBondProgram
end
end StatMech.Sharpness
