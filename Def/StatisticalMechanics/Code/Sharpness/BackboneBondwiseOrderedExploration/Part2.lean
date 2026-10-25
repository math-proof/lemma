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
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneBondwiseOrderedExploration
open Finset
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

namespace shb_DynamicEdgeExploration

variable {D B : Type*} [DecidableEq B]


def bondwiseOrdered (X : shb_DynamicEdgeExploration D B) :
    shb_OrderedLocalExploration D B B where
  tests := fun d => shb_bondwiseOrderedTests (X.edgeOrder d) (X.edgeOrder_nodup d)
  advance := X.advance

end shb_DynamicEdgeExploration
end StatMech.Sharpness
