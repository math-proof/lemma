/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Monotonic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.FKG
import Def.StatisticalMechanics.Code.OSSS.Monotonic.Part2
open Finset


namespace StatMech

namespace OSSS.Monotonic

variable {E : Type*} [Fintype E] [DecidableEq E]


lemma condNorm_pos {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (F : Finset E) (η : ConfigSpace E) : 0 < condNorm μ F η := by
  unfold condNorm
  refine Finset.sum_pos' (fun ω _ => ?_) ⟨η, Finset.mem_univ η, ?_⟩
  · split
    · exact (hpos ω).le
    · rfl
  · rw [if_pos (agree_self F η)]; exact hpos η


lemma condMass_nonneg {μ : ConfigSpace E → ℝ} (hμ : 0 ≤ μ) (F : Finset E)
    (η : ConfigSpace E) (hZ : 0 < condNorm μ F η) : 0 ≤ condMass μ F η := by
  intro ω
  unfold condMass
  apply div_nonneg _ hZ.le
  split
  · exact hμ ω
  · rfl


lemma condMass_sum {μ : ConfigSpace E → ℝ} (F : Finset E) (η : ConfigSpace E)
    (hZ : condNorm μ F η ≠ 0) : ∑ ω, condMass μ F η ω = 1 := by
  have h : ∑ ω, condMass μ F η ω
      = (∑ ω, (if Agree F η ω then μ ω else 0)) / condNorm μ F η := by
    unfold condMass; rw [Finset.sum_div]
  rw [h]
  exact div_self hZ


lemma cross_restricted {μ : ConfigSpace E → ℝ} (hμ : 0 ≤ μ)
    (hFKG : FKGLatticeCondition μ) (F : Finset E) (ξ ζ : ConfigSpace E)
    (hle : ∀ f ∈ F, ξ f ≤ ζ f) (a b : ConfigSpace E) :
    (if Agree F ξ a then μ a else 0) * (if Agree F ζ b then μ b else 0)
      ≤ (if Agree F ξ (a ⊓ b) then μ (a ⊓ b) else 0)
          * (if Agree F ζ (a ⊔ b) then μ (a ⊔ b) else 0) := by
  by_cases ha : Agree F ξ a
  · by_cases hb : Agree F ζ b
    · rw [if_pos ha, if_pos hb, if_pos (agree_inf F ξ ζ a b hle ha hb),
          if_pos (agree_sup F ξ ζ a b hle ha hb), mul_comm (μ (a ⊓ b))]
      exact hFKG a b
    · rw [if_neg hb, mul_zero]
      apply mul_nonneg <;> [split; split] <;> first | exact hμ _ | rfl
  · rw [if_neg ha, zero_mul]
    apply mul_nonneg <;> [split; split] <;> first | exact hμ _ | rfl


lemma cross_condMass {μ : ConfigSpace E → ℝ} (hμ : 0 ≤ μ)
    (hFKG : FKGLatticeCondition μ) (F : Finset E) (ξ ζ : ConfigSpace E)
    (hle : ∀ f ∈ F, ξ f ≤ ζ f) (hZξ : 0 < condNorm μ F ξ) (hZζ : 0 < condNorm μ F ζ)
    (a b : ConfigSpace E) :
    condMass μ F ξ a * condMass μ F ζ b
      ≤ condMass μ F ξ (a ⊓ b) * condMass μ F ζ (a ⊔ b) := by
  unfold condMass
  rw [div_mul_div_comm, div_mul_div_comm]
  exact div_le_div_of_nonneg_right (cross_restricted hμ hFKG F ξ ζ hle a b)
    (mul_pos hZξ hZζ).le


end OSSS.Monotonic
end StatMech
