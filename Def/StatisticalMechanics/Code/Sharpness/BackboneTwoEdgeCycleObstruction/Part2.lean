/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeBondToggle.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeCycleObstruction
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

def headEdge : graph.edgeFinset := ⟨s((0 : Fin 6), 1), by simp⟩

def suffixEdge : graph.edgeFinset := ⟨s((1 : Fin 6), 2), by simp⟩

def cycleEdge₀ : graph.edgeFinset := ⟨s((3 : Fin 6), 4), by simp⟩

def cycleEdge₁ : graph.edgeFinset := ⟨s((4 : Fin 6), 5), by simp⟩

def cycleEdge₂ : graph.edgeFinset := ⟨s((5 : Fin 6), 3), by simp⟩

end BackboneTwoEdgeCycleObstruction
end
end StatMech.Sharpness
