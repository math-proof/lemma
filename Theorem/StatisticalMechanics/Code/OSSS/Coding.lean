/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Coding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.Monotonic.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.OSSS.Part6
import Def.StatisticalMechanics.Code.OSSS.Coding
open scoped BigOperators
open Finset MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace OSSS.Coding

open OSSS.Monotonic

variable {E : Type*} [Fintype E] [DecidableEq E]


lemma condProbBit_true_add_false (μ : ConfigSpace E → ℝ) (F : Finset E)
    (η : ConfigSpace E) (e : E) (hF : condNorm μ F η ≠ 0) :
    condProbBit μ F η e true + condProbBit μ F η e false = 1 := by
  unfold condProbBit
  rw [← add_div, div_eq_one_iff_eq hF, ← Finset.sum_add_distrib]
  unfold condNorm
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hag : Agree F η ω
  · cases ω e <;> simp [hag]
  · simp [hag]


lemma condProbBit_nonneg {μ : ConfigSpace E → ℝ} (hμ : ∀ ω, 0 ≤ μ ω) (F : Finset E)
    (η : ConfigSpace E) (e : E) (b : Bool) (hF : 0 < condNorm μ F η) :
    0 ≤ condProbBit μ F η e b := by
  unfold condProbBit
  refine div_nonneg (Finset.sum_nonneg fun ω _ => ?_) hF.le
  split
  · exact hμ ω
  · rfl


lemma condProbBit_le_one {μ : ConfigSpace E → ℝ} (hμ : ∀ ω, 0 ≤ μ ω) (F : Finset E)
    (η : ConfigSpace E) (e : E) (b : Bool) (hF : 0 < condNorm μ F η) :
    condProbBit μ F η e b ≤ 1 := by
  cases b with
  | true =>
    have h1 := condProbBit_true_add_false μ F η e hF.ne'
    have h2 := condProbBit_nonneg hμ F η e false hF
    linarith
  | false =>
    have h1 := condProbBit_true_add_false μ F η e hF.ne'
    have h2 := condProbBit_nonneg hμ F η e true hF
    linarith


omit [Fintype E] [DecidableEq E] in
lemma agree_congr_of_eq_on (F : Finset E) (η η' ω : ConfigSpace E)
    (h : ∀ f ∈ F, η f = η' f) : Agree F η ω ↔ Agree F η' ω := by
  unfold Agree
  constructor <;> intro hyp f hf
  · rw [hyp f hf, h f hf]
  · rw [hyp f hf, ← h f hf]

lemma condNorm_congr (μ : ConfigSpace E → ℝ) (F : Finset E) (η η' : ConfigSpace E)
    (h : ∀ f ∈ F, η f = η' f) : condNorm μ F η = condNorm μ F η' := by
  unfold condNorm
  apply Finset.sum_congr rfl
  intro ω _
  exact if_congr (agree_congr_of_eq_on F η η' ω h) rfl rfl

lemma condProbBit_congr (μ : ConfigSpace E → ℝ) (F : Finset E) (η η' : ConfigSpace E)
    (e : E) (b : Bool) (h : ∀ f ∈ F, η f = η' f) :
    condProbBit μ F η e b = condProbBit μ F η' e b := by
  unfold condProbBit
  rw [condNorm_congr μ F η η' h]
  congr 1
  apply Finset.sum_congr rfl
  intro ω _
  exact if_congr (and_congr_left (fun _ => agree_congr_of_eq_on F η η' ω h)) rfl rfl

lemma condProbClosed_congr (μ : ConfigSpace E → ℝ) (F : Finset E) (η η' : ConfigSpace E)
    (e : E) (h : ∀ f ∈ F, η f = η' f) :
    condProbClosed μ F η e = condProbClosed μ F η' e :=
  condProbBit_congr μ F η η' e false h


end OSSS.Coding
end StatMech
