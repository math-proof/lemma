/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubleCoverClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompressionClose.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerIterationClose.Part4
import Def.StatisticalMechanics.Code.Inequalities.ReimerDoubleCoverClose
open Finset MeasureTheory
open scoped NNReal FinsetFamily


namespace StatMech

open ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


omit [Fintype α] [DecidableEq α] in

lemma bglue_agreeOn_true (K : α → Bool) (ω τ : ConfigSpace α) :
    agreeOn {a | K a = true} ω (bglue K ω τ) := by
  intro e he; simp only [Set.mem_setOf_eq] at he; simp only [bglue, he, if_true]

omit [Fintype α] [DecidableEq α] in


lemma bglue_agreeOn_false (K : α → Bool) (ω τ : ConfigSpace α) :
    agreeOn {a | K a = false} ω (bglue K τ ω) := by
  intro e he; simp only [Set.mem_setOf_eq] at he
  simp only [bglue, he]; rfl

omit [DecidableEq α] in


lemma bglue_weight (φ : α → Bool → ℝ) (K : α → Bool) (ω τ : ConfigSpace α) :
    pweight φ (bglue K ω τ) * pweight φ (bglue K τ ω) = pweight φ ω * pweight φ τ := by
  simp only [pweight, bglue]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun a _ => by by_cases h : K a <;> simp [h, mul_comm])

omit [Fintype α] [DecidableEq α] in


lemma bglue_bglue_left (K : α → Bool) (ω τ : ConfigSpace α) :
    bglue K (bglue K ω τ) (bglue K τ ω) = ω := by
  funext a; simp only [bglue]; by_cases h : K a <;> simp [h]

omit [Fintype α] [DecidableEq α] in

lemma bglue_bglue_right (K : α → Bool) (ω τ : ConfigSpace α) :
    bglue K (bglue K τ ω) (bglue K ω τ) = τ := by
  funext a; simp only [bglue]; by_cases h : K a <;> simp [h]


end StatMech
