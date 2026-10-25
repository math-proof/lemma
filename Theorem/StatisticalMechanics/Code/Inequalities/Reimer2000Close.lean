/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Reimer2000Close.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerPairWitnessClose.Part4
import Def.StatisticalMechanics.Code.Inequalities.Reimer2000Close
open Finset MeasureTheory
open scoped NNReal FinsetFamily


namespace StatMech

open ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


omit [Fintype α] [DecidableEq α] in
@[simp] lemma swapGlue_apply (S : α → Bool) (ω τ : ConfigSpace α) (a : α) :
    swapGlue S ω τ a = if S a then τ a else ω a := rfl

omit [DecidableEq α] in


lemma swapPair_weight (φ : α → Bool → ℝ) (S : α → Bool) (ω τ : ConfigSpace α) :
    pweight φ (swapGlue S ω τ) * pweight φ (swapGlue S τ ω) = pweight φ ω * pweight φ τ := by
  simp only [pweight, swapGlue]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun a _ => by by_cases h : S a <;> simp [h, mul_comm])

omit [Fintype α] [DecidableEq α] in


lemma swapGlue_swapGlue_left (S : α → Bool) (ω τ : ConfigSpace α) :
    swapGlue S (swapGlue S ω τ) (swapGlue S τ ω) = ω := by
  funext a; simp only [swapGlue]; by_cases h : S a <;> simp [h]

omit [Fintype α] [DecidableEq α] in

lemma swapGlue_swapGlue_right (S : α → Bool) (ω τ : ConfigSpace α) :
    swapGlue S (swapGlue S τ ω) (swapGlue S ω τ) = τ := by
  funext a; simp only [swapGlue]; by_cases h : S a <;> simp [h]


end StatMech
