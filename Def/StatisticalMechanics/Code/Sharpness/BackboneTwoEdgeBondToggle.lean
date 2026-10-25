/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondToggle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeBondProgram.Part9
import Instance.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeBondToggle
open SimpleGraph Finset
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneTwoEdgeBondToggle

open BackboneConcreteSelector

open BackboneConcreteBondProgram

open BackboneTwoEdgeBondProgram

open BackboneDeterminedCutSwitching

open BackboneP2CoordinateReindex

open FluxEdgeCopy

def firstCopy (G : SimpleGraph V) (e f : G.edgeFinset) (hne : e ≠ f) :
    Copy G (twoUnitFlux G e f) :=
  ⟨e, ⟨0, by simp [twoUnitFlux, unitFlux]⟩⟩


def secondCopy (G : SimpleGraph V) (e f : G.edgeFinset) (hne : e ≠ f) :
    Copy G (twoUnitFlux G e f) :=
  ⟨f, ⟨0, by simp [twoUnitFlux, unitFlux, hne]⟩⟩

end BackboneTwoEdgeBondToggle
end
end StatMech.Sharpness
