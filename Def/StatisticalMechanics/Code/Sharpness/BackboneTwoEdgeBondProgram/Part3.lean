/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondProgram.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneConcreteBondProgram.Part9
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeBondProgram.Part2
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

def sourceClass (_d : shb_ExplorationDomain V) :
    List (shb_ExplorationSegment V) -> Finset V
  | [] => ∅
  | [s] => {s.1, s.2.1}
  | [s, t] => {s.1, s.2.1} ∆ {t.1, t.2.1}
  | _ => ∅

end BackboneTwoEdgeBondProgram
end
end StatMech.Sharpness
