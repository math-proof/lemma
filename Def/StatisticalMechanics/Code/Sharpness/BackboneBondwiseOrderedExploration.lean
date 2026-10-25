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
open Finset
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

def shb_bondwiseOrderedTests {B : Type*} [DecidableEq B]
    (order : List B) (hnodup : order.Nodup) : shb_OrderedLocalTests B B where
  order := order
  order_nodup := hnodup
  exposure := fun b => {b}
  test := fun omega b => omega b
  test_local := by
    intro omega eta b hagree
    exact hagree b (Set.mem_singleton b)

end StatMech.Sharpness
