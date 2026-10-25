/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteBondProgram.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Sharpness.BackboneAsymmetricCoordinateCertificate.Part13
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneConcreteBondProgram.Part8
open SimpleGraph Finset

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneConcreteBondProgram

open BackboneConcreteSelector

open BackboneDeterminedCutSwitching

def ProgramRealizes
    (P : BondwiseSegmentProgram V)
    (S : shb_PartialCurrentDynamicSelector (V := V)) : Prop :=
  ∃ R : CompleteBondwiseSelectorSpec P,
    ∀ (d : shb_ExplorationDomain V)
      (word : List (shb_ExplorationSegment V))
      (m : d.graph.edgeFinset -> Nat),
      R.toPartialSelector.Fiber d word m <-> S.Fiber d word m


end BackboneConcreteBondProgram
end
end StatMech.Sharpness
