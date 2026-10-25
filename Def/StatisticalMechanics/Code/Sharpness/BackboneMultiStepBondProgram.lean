/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneMultiStepBondProgram.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneConcreteBondProgram.Part9
import Instance.StatisticalMechanics.Code.Sharpness.BackboneMultiStepBondProgram
open SimpleGraph Finset
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneMultiStepBondProgram

open BackboneConcreteSelector

open BackboneConcreteBondProgram

open BackboneDeterminedCutSwitching

def segmentEnds (s : shb_ExplorationSegment V) : Finset V :=
  {s.1, s.2.1}


def pairSourceClass (s t : shb_ExplorationSegment V) : Finset V :=
  segmentEnds s ∆ segmentEnds t


def sourceClass (_d : shb_ExplorationDomain V) :
    List (shb_ExplorationSegment V) -> Finset V
  | [] => ∅
  | [s, t] => pairSourceClass s t
  | _ => ∅

end BackboneMultiStepBondProgram
end
end StatMech.Sharpness
