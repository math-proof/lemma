/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeBondToggle.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeCycleObstruction.Part4
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

attribute [simp] headEdge_ne_suffixEdge headEdge_ne_cycleEdge₀
  headEdge_ne_cycleEdge₁ headEdge_ne_cycleEdge₂
  suffixEdge_ne_cycleEdge₀ suffixEdge_ne_cycleEdge₁
  suffixEdge_ne_cycleEdge₂ cycleEdge₀_ne_cycleEdge₁
  cycleEdge₀_ne_cycleEdge₂ cycleEdge₁_ne_cycleEdge₂
  suffixEdge_ne_headEdge cycleEdge₀_ne_headEdge cycleEdge₁_ne_headEdge
  cycleEdge₂_ne_headEdge cycleEdge₀_ne_suffixEdge
  cycleEdge₁_ne_suffixEdge cycleEdge₂_ne_suffixEdge
  cycleEdge₁_ne_cycleEdge₀ cycleEdge₂_ne_cycleEdge₀
  cycleEdge₂_ne_cycleEdge₁


def headSplit : Finset (Copy domain.graph superposition) :=
  univ.filter (fun i => i.2.val < unitFlux domain.graph headEdge i.1)


def oddCycleSplit : Finset (Copy domain.graph superposition) :=
  univ.filter (fun i => i.2.val < oddCycleFlux i.1)

end BackboneTwoEdgeCycleObstruction
end
end StatMech.Sharpness
