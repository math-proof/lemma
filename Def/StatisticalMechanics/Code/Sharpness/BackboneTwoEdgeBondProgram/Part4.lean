/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondProgram.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneConcreteBondProgram.Part9
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeBondProgram.Part3
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

noncomputable def selectorSpec :
    CompleteBondwiseSelectorSpec (V := V) (program (V := V)) where
  sourceClass := sourceClass (V := V)
  sourceClass_nil := sourceClass_nil
  complete_functional := program_complete_functional
  sources_eq_sourceClass_of_complete :=
    sources_eq_sourceClass_of_program_complete
  complete_nil_iff := program_complete_nil_iff
  head_active_of_complete := head_active_of_program_complete


end BackboneTwoEdgeBondProgram
end
end StatMech.Sharpness
