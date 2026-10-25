/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteBondProgram.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Sharpness.BackboneAsymmetricCoordinateCertificate.Part13
import Instance.StatisticalMechanics.Code.Sharpness.BackboneConcreteBondProgram
open SimpleGraph Finset

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneConcreteBondProgram

open BackboneConcreteSelector

open BackboneDeterminedCutSwitching

structure SelectorRealization
    (P : BondwiseSegmentProgram V)
    (S : shb_PartialCurrentDynamicSelector (V := V)) where
  complete_iff_fiber : ∀ d word m,
    P.CompleteEvent d word m <-> S.Fiber d word m


end BackboneConcreteBondProgram
end
end StatMech.Sharpness
