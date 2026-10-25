/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeExhaustiveProgram.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeCycleObstruction.Part9
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeExhaustiveProgram
open SimpleGraph Finset
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneTwoEdgeExhaustiveProgram

open BackboneConcreteBondProgram

open BackboneConcreteSelector

open BackboneDeterminedCutSwitching

open BackboneLabeledSwitching

open BackboneP2CoordinateReindex

open FluxEdgeCopy

noncomputable def selectorSpec :
    CompleteBondwiseSelectorSpec (V := V) (program (V := V)) where
  sourceClass := BackboneTwoEdgeBondProgram.sourceClass (V := V)
  sourceClass_nil := BackboneTwoEdgeBondProgram.sourceClass_nil
  complete_functional := program_complete_functional
  sources_eq_sourceClass_of_complete :=
    sources_eq_sourceClass_of_program_complete
  complete_nil_iff := program_complete_nil_iff
  head_active_of_complete := head_active_of_program_complete


end BackboneTwoEdgeExhaustiveProgram
end
end StatMech.Sharpness
