/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/FiniteMoments.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.RussoHamming.Part2
import Def.StatisticalMechanics.Code.BeffaraDC.FiniteMoments.Part2


namespace StatMech

namespace BeffaraDC

open ConfigSpace Function Finset

variable {E : Type*} [Fintype E] [DecidableEq E]


theorem expHammingMoment_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A : Set (ConfigSpace E)) (t : ℝ) : 0 ≤ expHammingMoment p A t :=
  expect_nonneg hp0 hp1 (fun _ => (Real.exp_pos _).le)


theorem exp_hammingMoment_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A : Set (ConfigSpace E)) {t : ℝ} (ht : 0 ≤ t) :
    expHammingMoment p A t ≤ Real.exp (t * (Fintype.card E : ℝ)) := by
  unfold expHammingMoment
  refine expect_le_const hp0 hp1 (fun ω => ?_)
  refine Real.exp_le_exp.mpr ?_
  exact mul_le_mul_of_nonneg_left (hammingToSet_real_le_card A ω) ht


theorem hammingMoment_one (p : ℝ) (A : Set (ConfigSpace E)) :
    hammingMoment p A 1 = expect p (fun ω => (hammingToSet A ω : ℝ)) := by
  unfold hammingMoment
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  simp only [pow_one]


theorem first_moment_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A : Set (ConfigSpace E)) :
    0 ≤ expect p (fun ω => (hammingToSet A ω : ℝ)) :=
  expect_nonneg hp0 hp1 (fun ω => by positivity)


theorem prob_le_first_moment {p₁ p₂ : ℝ} (hp1 : 0 < p₁) (hp12 : p₁ < p₂) (hp2 : p₂ < 1)
    (A : Set (ConfigSpace E)) (hA : IsIncreasing A) :
    prob p₁ A ≤ prob p₂ A *
      Real.exp (- 4 * (p₂ - p₁) * expect p₂ (fun ω => (hammingToSet A ω : ℝ))) :=
  russoHammingIntegrated hp1 hp12 hp2 A hA

end BeffaraDC
end StatMech
