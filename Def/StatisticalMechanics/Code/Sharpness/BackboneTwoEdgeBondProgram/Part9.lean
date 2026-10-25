/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondProgram.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneConcreteBondProgram.Part9
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeBondProgram.Part8
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

def fin3PathFlux : fin3PathDomain.graph.edgeFinset -> Nat :=
  twoUnitFlux fin3PathDomain.graph fin3LeftEdge fin3RightEdge


def fin3LeftFirst : Prop :=
  scan.firstAdmissible
      (fun _ b => fluxBitConfig fin3PathDomain.graph
        BackboneConcreteBondProgram.oddBit fin3PathFlux b)
      ⟨fin3PathDomain, []⟩ = some fin3LeftEdge.1


def fin3RightFirst : Prop :=
  scan.firstAdmissible
      (fun _ b => fluxBitConfig fin3PathDomain.graph
        BackboneConcreteBondProgram.oddBit fin3PathFlux b)
      ⟨fin3PathDomain, []⟩ = some fin3RightEdge.1


end BackboneTwoEdgeBondProgram
end
end StatMech.Sharpness
