/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerEndpointProve.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompression.Part5
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part6
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompressLib.Part2
import Def.StatisticalMechanics.Code.Inequalities.ReimerEndpointProve.Part2
open Finset MeasureTheory
open scoped NNReal


namespace StatMech

open ConfigSpace

variable {α : Type*}


@[simp] lemma mem_leftEvent {A : Set (ConfigSpace α)} {ω : ConfigSpace (α ⊕ α)} :
    ω ∈ leftEvent A ↔ leftCfg ω ∈ A := Iff.rfl

@[simp] lemma mem_rightEvent {B : Set (ConfigSpace α)} {ω : ConfigSpace (α ⊕ α)} :
    ω ∈ rightEvent B ↔ rightCfg ω ∈ B := Iff.rfl


lemma leftCfg_eq_of_agreeOn_leftBlock {ω ω' : ConfigSpace (α ⊕ α)}
    (h : agreeOn (leftBlock (α := α)) ω ω') : leftCfg ω' = leftCfg ω := by
  funext a
  exact h (Sum.inl a) (by simp [leftBlock, Sum.isLeft])


lemma rightCfg_eq_of_agreeOn_rightBlock {ω ω' : ConfigSpace (α ⊕ α)}
    (h : agreeOn (rightBlock (α := α)) ω ω') : rightCfg ω' = rightCfg ω := by
  funext a
  exact h (Sum.inr a) (by simp [rightBlock, Sum.isRight])


theorem dependsOn_leftEvent (A : Set (ConfigSpace α)) :
    DependsOn (leftEvent A) (leftBlock (α := α)) := by
  intro ω ω' hag
  simp only [mem_leftEvent]
  rw [leftCfg_eq_of_agreeOn_leftBlock hag]


theorem dependsOn_rightEvent (B : Set (ConfigSpace α)) :
    DependsOn (rightEvent B) (rightBlock (α := α)) := by
  intro ω ω' hag
  simp only [mem_rightEvent]
  rw [rightCfg_eq_of_agreeOn_rightBlock hag]


section Support

variable [DecidableEq α]


theorem leftCfg_supportCfg_dbl (S T : Finset α) :
    leftCfg (supportCfg (dbl S T)) = supportCfg S := by
  funext a
  simp only [leftCfg, supportCfg_apply, mem_dbl_inl]


theorem rightCfg_supportCfg_dbl (S T : Finset α) :
    rightCfg (supportCfg (dbl S T)) = supportCfg T := by
  funext a
  simp only [rightCfg, supportCfg_apply, mem_dbl_inr]

end Support
end StatMech
