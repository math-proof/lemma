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
import Def.StatisticalMechanics.Code.Sharpness.BackboneBondwiseOrderedExploration
open Finset
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

namespace shb_bondwiseOrderedTests

variable {B : Type*} [DecidableEq B]

@[simp] theorem test_apply (order : List B) (hnodup : order.Nodup)
    (omega : B -> Bool) (b : B) :
    (shb_bondwiseOrderedTests order hnodup).test omega b = omega b := rfl

@[simp] theorem exposure_apply (order : List B) (hnodup : order.Nodup)
    (b : B) :
    (shb_bondwiseOrderedTests order hnodup).exposure b = {b} := rfl


theorem mem_determinedCut_iff (order : List B) (hnodup : order.Nodup)
    (accepted b : B) :
    b ∈ (shb_bondwiseOrderedTests order hnodup).determinedCut accepted <->
      b ∈ (shb_bondwiseOrderedTests order hnodup).testedThrough accepted := by
  constructor
  · rintro ⟨e, he, hb⟩
    simpa only [exposure_apply, Set.mem_singleton_iff] using hb ▸ he
  · intro hb
    exact ⟨b, hb, Set.mem_singleton b⟩


theorem rejected_mem_determinedCut (order : List B) (hnodup : order.Nodup)
    (accepted rejected : B)
    (hrejected : rejected ∈ order.takeWhile (fun b => b != accepted)) :
    rejected ∈ (shb_bondwiseOrderedTests order hnodup).determinedCut accepted := by
  rw [mem_determinedCut_iff]
  exact List.mem_append_left _ hrejected


theorem accepted_mem_determinedCut (order : List B) (hnodup : order.Nodup)
    (accepted : B) :
    accepted ∈ (shb_bondwiseOrderedTests order hnodup).determinedCut accepted := by
  rw [mem_determinedCut_iff]
  exact shb_OrderedLocalTests.accepted_mem_testedThrough _ _

end shb_bondwiseOrderedTests
end StatMech.Sharpness
