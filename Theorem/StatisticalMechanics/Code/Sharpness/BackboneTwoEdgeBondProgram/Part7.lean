/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondProgram.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneConcreteBondProgram.Part9
import Def.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeBondProgram.Part7
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

theorem fin3LeftEdge_ne_rightEdge : fin3LeftEdge ≠ fin3RightEdge := by
  intro h
  have hv := congrArg Subtype.val h
  exact (by decide :
    s((0 : Fin 3), 1) ≠ s((1 : Fin 3), 2)) (by
      simpa [fin3LeftEdge, fin3RightEdge] using hv)


end BackboneTwoEdgeBondProgram
end
end StatMech.Sharpness
