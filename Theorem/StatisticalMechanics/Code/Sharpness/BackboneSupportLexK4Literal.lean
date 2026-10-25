/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexK4Literal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSupportLexK4Realization.Part9
import Def.StatisticalMechanics.Code.Sharpness.BackboneSupportLexK4Literal
open Finset SimpleGraph
open scoped BigOperators

set_option maxHeartbeats 1600000


namespace StatMech.Sharpness

theorem shb_summable_currentTerm (x : ℝ) :
    Summable (shbCurrentTerm x) := by
  have h := NormedSpace.expSeries_summable' (𝕂 := ℝ) x
  exact h.congr (fun k => by simp [shbCurrentTerm, div_eq_inv_mul, mul_comm])

theorem shb_summable_currentTerm_filter (x : ℝ) (Q : ℕ → Prop)
    [DecidablePred Q] :
    Summable (fun k => if Q k then shbCurrentTerm x k else 0) := by
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
    (shb_summable_currentTerm x).norm
  split <;> simp

theorem shb_tsum_even_filter (x : ℝ) :
    (∑' k : ℕ, if Even k then shbCurrentTerm x k else 0) =
      shbEvenCurrentSeries x := by
  unfold shbEvenCurrentSeries
  apply tsum_eq_tsum_of_ne_zero_bij
    (fun k : ↑(Function.support (fun n : ℕ =>
      shbCurrentTerm x (2 * n))) => 2 * k.1)
  · intro a b hab
    apply Subtype.ext
    dsimp at hab ⊢
    omega
  · intro k hk
    simp only [Function.mem_support] at hk
    have he : Even k := by
      by_contra hne
      rw [if_neg hne] at hk
      exact hk rfl
    obtain ⟨n, rfl⟩ := he
    have hterm : shbCurrentTerm x (n + n) ≠ 0 := by simpa using hk
    exact ⟨⟨n, by simpa [two_mul] using hterm⟩, by simp [two_mul]⟩
  · intro k
    simp [shbCurrentTerm]

theorem shb_tsum_odd_filter (x : ℝ) :
    (∑' k : ℕ, if Odd k then shbCurrentTerm x k else 0) =
      shbOddCurrentSeries x := by
  unfold shbOddCurrentSeries
  apply tsum_eq_tsum_of_ne_zero_bij
    (fun k : ↑(Function.support (fun n : ℕ =>
      shbCurrentTerm x (2 * n + 1))) => 2 * k.1 + 1)
  · intro a b hab
    apply Subtype.ext
    dsimp at hab ⊢
    omega
  · intro k hk
    simp only [Function.mem_support] at hk
    have ho : Odd k := by
      by_contra hne
      rw [if_neg hne] at hk
      exact hk rfl
    obtain ⟨n, hn⟩ := ho
    refine ⟨⟨n, ?_⟩, hn.symm⟩
    simpa [hn] using hk
  · intro k
    simp [shbCurrentTerm]


end StatMech.Sharpness
