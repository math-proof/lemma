/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/FiniteMoments.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.RussoHamming.Part2


namespace StatMech

namespace BeffaraDC

open ConfigSpace Function Finset

variable {E : Type*} [Fintype E] [DecidableEq E]


omit [DecidableEq E] in


theorem hammingToSet_le_card (A : Set (ConfigSpace E)) (ω : ConfigSpace E) :
    hammingToSet A ω ≤ Fintype.card E := by
  rcases A.eq_empty_or_nonempty with rfl | hne
  · simp [hammingToSet]
  · obtain ⟨a, _, ha⟩ := exists_realizer A hne ω
    rw [← ha]
    exact hammingDist_le_card_fintype

omit [DecidableEq E] in

theorem hammingToSet_real_le_card (A : Set (ConfigSpace E)) (ω : ConfigSpace E) :
    (hammingToSet A ω : ℝ) ≤ (Fintype.card E : ℝ) := by
  exact_mod_cast hammingToSet_le_card A ω


theorem expect_const (p : ℝ) (c : ℝ) :
    expect p (fun _ : ConfigSpace E => c) = c := by
  unfold expect
  simp only []
  rw [← Finset.mul_sum, configWeight_sum_one, mul_one]


theorem expect_le_const {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {c : ℝ}
    {f : ConfigSpace E → ℝ} (h : ∀ ω, f ω ≤ c) : expect p f ≤ c :=
  (expect_mono hp0 hp1 h).trans_eq (expect_const p c)


end BeffaraDC
end StatMech
