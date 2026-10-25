/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteBondProgram.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Sharpness.BackboneAsymmetricCoordinateCertificate.Part13
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneConcreteBondProgram.Part7
open SimpleGraph Finset

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneConcreteBondProgram

open BackboneConcreteSelector

open BackboneDeterminedCutSwitching

noncomputable def completeSpecRealization :
    SelectorRealization (program (V := V))
      (completeSpec (V := V)).toPartialSelector where
  complete_iff_fiber := by
    intro d word m
    exact ((completeSpec (V := V)).fiber_iff_completeEvent d word m).symm


end BackboneConcreteBondProgram
end
end StatMech.Sharpness
