/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeExhaustiveProgram.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeCycleObstruction.Part9
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeExhaustiveProgram.Part2
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

namespace Cycle

open BackboneTwoEdgeCycleObstruction


def oddTrianglePairFlux : domain.graph.edgeFinset -> Nat := fun g =>
  BackboneTwoEdgeBondProgram.twoUnitFlux domain.graph headEdge suffixEdge g +
    oddCycleFlux g

end Cycle
end BackboneTwoEdgeExhaustiveProgram
end
end StatMech.Sharpness
