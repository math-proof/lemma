/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma4Return.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.ShermanLoop
import Theorem.StatisticalMechanics.Code.Onsager.ShermanLemma4.Part3


namespace StatMech.Onsager

open Matrix BigOperators Finset Complex

set_option linter.unusedSectionVars false

section Analytic

theorem ons_one_sub_ne_zero_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) : (1 : ℂ) - z ≠ 0 := by
  rw [sub_ne_zero]
  intro h
  rw [← h] at hz
  simp at hz


theorem ons_lemma4_geometric {z : ℂ} (hz : ‖z‖ < 1) :
    ∑' k : ℕ, z ^ (k + 1) / (k + 1) = -Complex.log (1 - z) :=
  ons_tsum_shifted_pow_div hz


theorem ons_lemma4_exp {z : ℂ} (hz : ‖z‖ < 1) :
    Complex.exp (-(∑' k : ℕ, z ^ (k + 1) / (k + 1))) = 1 - z := by
  rw [ons_lemma4_geometric hz, neg_neg]
  exact Complex.exp_log (ons_one_sub_ne_zero_of_norm_lt_one hz)

end Analytic

section AlgebraicTuple


theorem ons_pow_eq_sum_tuple {α : Type*} [DecidableEq α] (S : Finset α) (wt : α → ℂ) (k : ℕ) :
    (∑ s ∈ S, wt s) ^ k
      = ∑ p ∈ Fintype.piFinset (fun _ : Fin k => S), ∏ i : Fin k, wt (p i) :=
  Finset.sum_pow' S wt k

end AlgebraicTuple
end StatMech.Onsager
