/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/PerOrbitCardClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerSwapInjClose.Part3
import Def.StatisticalMechanics.Code.Inequalities.PerOrbitCardClose.Part5
open Finset MeasureTheory
open scoped NNReal FinsetFamily


namespace StatMech

open ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


theorem poc_slabCard_top_iff_reimerCardForm (A B : Set (ConfigSpace α)) :
    #(poc_slabBox A B poc_topKey) ≤ #(poc_slabImg A B poc_topKey) ↔ poc_ReimerCardForm A B := by
  rw [poc_slabBox_top, poc_slabImg_top]; rfl


theorem poc_reimerCardForm_of_slabCard (A B : Set (ConfigSpace α))
    (h : poc_SlabCard A B) : poc_ReimerCardForm A B :=
  (poc_slabCard_top_iff_reimerCardForm A B).mp (h poc_topKey)


omit [Fintype α] [DecidableEq α] in


theorem poc_membership (A B : Set (ConfigSpace α)) (ω τ : ConfigSpace α)
    (wK : α → Bool) (hA : OccursOn A {a | wK a = true} ω)
    (wL : α → Bool) (hB : OccursOn B {a | wL a = true} ω)
    (hdis : ∀ a, wK a = true → wL a = false) :
    swapGlue (fun a => !wK a) ω τ ∈ A ∧ swapGlue (fun a => !wK a) τ ω ∈ B := by
  refine ⟨hA _ ?_, hB _ ?_⟩
  · intro a ha
    simp only [Set.mem_setOf_eq] at ha
    simp only [swapGlue_apply, ha, Bool.not_true, Bool.false_eq_true, if_false]
  · intro a ha
    simp only [Set.mem_setOf_eq] at ha
    have haK : wK a = false := by
      cases hkk : wK a with
      | false => rfl
      | true => rw [hdis a hkk] at ha; exact absurd ha (by simp)
    simp only [swapGlue_apply, haK, Bool.not_false, if_true]


end StatMech
