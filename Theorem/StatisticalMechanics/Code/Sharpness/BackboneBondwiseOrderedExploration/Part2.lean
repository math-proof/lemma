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
import Def.StatisticalMechanics.Code.Sharpness.BackboneBondwiseOrderedExploration.Part2
open Finset
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

namespace shb_DynamicEdgeExploration

variable {D B : Type*} [DecidableEq B]


@[simp] theorem bondwiseOrdered_tests_order
    (X : shb_DynamicEdgeExploration D B) (d : D) :
    ((X.bondwiseOrdered).tests d).order = X.edgeOrder d := rfl

@[simp] theorem bondwiseOrdered_advance
    (X : shb_DynamicEdgeExploration D B) (d : D) (b : B) :
    X.bondwiseOrdered.advance d b = X.advance d b := rfl


theorem bondwiseOrdered_selects_iff
    (X : shb_DynamicEdgeExploration D B) (omega : B -> Bool)
    (d : D) (word : List B) :
    X.bondwiseOrdered.Selects omega d word <->
      X.Selects (fun _ b => omega b) d word := by
  induction word generalizing d with
  | nil => simp
  | cons b bs ih =>
      simp only [shb_OrderedLocalExploration.selects_cons, selects_cons,
        bondwiseOrdered, shb_bondwiseOrderedTests, firstAdmissible]
      exact and_congr Iff.rfl (ih (X.advance d b))


theorem mem_bondwiseOrdered_determinedCut_iff
    (X : shb_DynamicEdgeExploration D B) (d : D) (accepted b : B) :
    b ∈ ((X.bondwiseOrdered).tests d).determinedCut accepted <->
      b ∈ X.determinedAt d accepted := by
  change b ∈ (shb_bondwiseOrderedTests (X.edgeOrder d)
      (X.edgeOrder_nodup d)).determinedCut accepted <-> _
  rw [shb_bondwiseOrderedTests.mem_determinedCut_iff]
  have hpred : (fun e : B => e != accepted) =
      (fun e : B => decide (e ≠ accepted)) := by
    funext e
    by_cases h : e = accepted <;> simp [h]
  simp only [shb_OrderedLocalTests.testedThrough, determinedAt,
    shb_bondwiseOrderedTests]
  rw [hpred]


theorem mem_bondwiseOrdered_traceCut_iff
    (X : shb_DynamicEdgeExploration D B) (d : D) (word : List B) (b : B) :
    b ∈ X.bondwiseOrdered.traceCut d word <->
      b ∈ X.determinedTrace d word := by
  induction word generalizing d with
  | nil => simp
  | cons accepted rest ih =>
      rw [shb_OrderedLocalExploration.traceCut_cons, determinedTrace_cons]
      simp only [Set.mem_union, List.mem_append]
      rw [mem_bondwiseOrdered_determinedCut_iff]
      exact or_congr Iff.rfl (ih (X.advance d accepted))


theorem selects_iff_of_agreeOn_determinedTrace
    (X : shb_DynamicEdgeExploration D B) (omega eta : B -> Bool)
    (d : D) (word : List B)
    (hagree : ∀ b ∈ X.determinedTrace d word, omega b = eta b) :
    X.Selects (fun _ b => omega b) d word <->
      X.Selects (fun _ b => eta b) d word := by
  rw [← X.bondwiseOrdered_selects_iff omega d word,
    ← X.bondwiseOrdered_selects_iff eta d word]
  apply X.bondwiseOrdered.selects_iff_of_agreeOn_traceCut
  intro b hb
  exact hagree b ((X.mem_bondwiseOrdered_traceCut_iff d word b).mp hb)

end shb_DynamicEdgeExploration
end StatMech.Sharpness
