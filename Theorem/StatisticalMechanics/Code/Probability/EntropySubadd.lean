/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/EntropySubadd.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.PBiasedTensorize.Part11
import Def.StatisticalMechanics.Code.Probability.EntropySubadd
open scoped BigOperators
open Finset
open Real

set_option linter.style.longLine false


namespace StatMech.Probability

open StatMech StatMech.OSSS


@[simp] theorem esd_Phi_zero : esd_Phi 0 = 0 := by simp [esd_Phi]

theorem esd_Phi_eq (x : ℝ) : esd_Phi x = x * Real.log x := rfl


theorem esd_logSum {ι : Type*} (t : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ t, 0 ≤ a i) (hb : ∀ i ∈ t, 0 < b i)
    (hA : 0 < ∑ i ∈ t, a i) :
    (∑ i ∈ t, a i) * Real.log ((∑ i ∈ t, a i) / (∑ i ∈ t, b i))
      ≤ ∑ i ∈ t, a i * Real.log (a i / b i) := by
  have htne : t.Nonempty := by
    rcases Finset.eq_empty_or_nonempty t with h | h
    · rw [h] at hA; simp at hA
    · exact h
  set A := ∑ i ∈ t, a i with hAdef
  set B := ∑ i ∈ t, b i with hBdef
  have hBpos : 0 < B := Finset.sum_pos hb htne
  have hpt : ∀ i ∈ t, a i * Real.log (A / B) + a i - b i * (A / B)
      ≤ a i * Real.log (a i / b i) := by
    intro i hi
    rcases eq_or_lt_of_le (ha i hi) with h0 | hpos
    · rw [← h0]
      have hbi := hb i hi
      simp only [zero_mul, zero_add, zero_sub]
      have : 0 ≤ b i * (A / B) := by positivity
      linarith
    · have hbi := hb i hi
      have hgibbs : 1 - (b i * A) / (a i * B) ≤ Real.log ((a i * B) / (b i * A)) := by
        have hle := Real.log_le_sub_one_of_pos (show (0:ℝ) < (b i * A)/(a i * B) by positivity)
        have hrw : Real.log ((b i * A)/(a i * B)) = - Real.log ((a i * B)/(b i * A)) := by
          rw [← Real.log_inv]; congr 1; rw [inv_div]
        rw [hrw] at hle
        nlinarith [hle]
      have hlogeq : Real.log (a i / b i) - Real.log (A/B) = Real.log ((a i * B)/(b i * A)) := by
        rw [← Real.log_div (by positivity) (by positivity)]
        congr 1
        rw [div_div_div_eq, mul_comm (a i) B, mul_comm (b i) A]
      have hmul : a i * (1 - (b i * A)/(a i * B)) ≤ a i * (Real.log (a i / b i) - Real.log (A/B)) := by
        apply mul_le_mul_of_nonneg_left _ hpos.le
        rw [hlogeq]; exact hgibbs
      have hexpand : a i * (1 - (b i * A)/(a i * B)) = a i - b i * (A/B) := by
        field_simp
      nlinarith [hmul, hexpand]
  have hsum := Finset.sum_le_sum hpt
  have hlhs : (∑ i ∈ t, (a i * Real.log (A / B) + a i - b i * (A / B)))
      = A * Real.log (A/B) := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ← hAdef]
    rw [show (∑ i ∈ t, b i * (A/B)) = B * (A/B) by rw [← Finset.sum_mul, ← hBdef]]
    rw [show B * (A/B) = A by field_simp]
    ring
  rw [hlhs] at hsum
  exact hsum


end StatMech.Probability
