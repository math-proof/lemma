/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondProgram.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneConcreteBondProgram.Part9
import Def.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeBondProgram.Part8
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

@[simp] theorem fin3PathDomain_graph : fin3PathDomain.graph = fin3PathGraph :=
  rfl

@[simp] theorem fin3LeftEdge_active :
    canonicalEdgeSegment fin3PathGraph fin3LeftEdge ∈
      fin3PathDomain.active := by
  simp [fin3PathDomain]

@[simp] theorem fin3RightEdge_active :
    canonicalEdgeSegment fin3PathGraph fin3RightEdge ∈
      fin3PathDomain.active := by
  simp [fin3PathDomain]


end BackboneTwoEdgeBondProgram
end
end StatMech.Sharpness
