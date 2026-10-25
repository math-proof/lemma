/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneBondwiseOrderedExploration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneExplorationSelector.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneOrderedDeterminedCut.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneActualSelectorSwitching.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneBondwiseOrderedExploration.Part2
open Finset
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

namespace BackboneDeterminedCutSwitching

open FluxEdgeCopy

open BackboneLabeledSwitching

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

variable {D : Type*}

noncomputable local instance shb_bondwiseDecidableAdj (H : SimpleGraph V) :
    DecidableRel H.Adj := Classical.decRel _


end BackboneDeterminedCutSwitching
end StatMech.Sharpness
