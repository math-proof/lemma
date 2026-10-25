/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeBondToggle.Part3
import Instance.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeCycleObstruction
open SimpleGraph Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

namespace BackboneTwoEdgeCycleObstruction

open BackboneConcreteBondProgram

open BackboneConcreteSelector

open BackboneDeterminedCutSwitching

open BackboneLabeledSwitching

open BackbonePartialP2Reindex

open BackboneP2CoordinateReindex

open BackboneTwoEdgeBondProgram

open BackboneTwoEdgeBondToggle

open FluxEdgeCopy

def graph : SimpleGraph (Fin 6) :=
  SimpleGraph.fromEdgeSet
    ({s((0 : Fin 6), 1), s((1 : Fin 6), 2), s((3 : Fin 6), 4),
        s((4 : Fin 6), 5), s((5 : Fin 6), 3)} : Set (Sym2 (Fin 6)))

end BackboneTwoEdgeCycleObstruction
end
end StatMech.Sharpness
