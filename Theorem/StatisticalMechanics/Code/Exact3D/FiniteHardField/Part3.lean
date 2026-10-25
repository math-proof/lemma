/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteHardField.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.StatisticalMechanics.Code.Exact3D.FiniteHardField.Part3
open Filter
open scoped BigOperators Topology


namespace StatMech

namespace Exact3D

theorem countHardFieldFactor_tendsto {α : Type*}
    (penalty : α → ℕ) {scale : ℝ} (hscale : 0 < scale) (a : α) :
    Tendsto (fun H : ℝ => countHardFieldFactor penalty scale H a)
      atTop
      (𝓝 (countHardFieldLimitFactor penalty a)) := by
  by_cases hzero : penalty a = 0
  · simp [countHardFieldFactor, countHardFieldLimitFactor, hzero]
  · have hpenNat : 0 < penalty a := Nat.pos_of_ne_zero hzero
    have hpenReal : 0 < (penalty a : ℝ) := by
      exact_mod_cast hpenNat
    have hscalePenalty : 0 < scale * (penalty a : ℝ) :=
      mul_pos hscale hpenReal
    have hmul :
        Tendsto (fun H : ℝ => H * (scale * (penalty a : ℝ)))
          atTop atTop := by
      simpa using
        (Filter.Tendsto.atTop_mul_const hscalePenalty
          (Filter.tendsto_id : Tendsto (fun H : ℝ => H) atTop atTop))
    have hneg :
        Tendsto (fun H : ℝ => -(H * (scale * (penalty a : ℝ))))
          atTop atBot :=
      Filter.tendsto_neg_atTop_atBot.comp hmul
    have hexp :
        Tendsto
          (fun H : ℝ => Real.exp (-(H * (scale * (penalty a : ℝ)))))
          atTop
          (𝓝 0) :=
      Real.tendsto_exp_atBot.comp hneg
    have hrewrite :
        (fun H : ℝ => countHardFieldFactor penalty scale H a)
          =
        (fun H : ℝ => Real.exp (-(H * (scale * (penalty a : ℝ))))) := by
      funext H
      simp [countHardFieldFactor]
      ring_nf
    simpa [countHardFieldLimitFactor, hzero, hrewrite] using hexp


theorem countHardFieldRatio_tendsto {α : Type*} (s : Finset α)
    (penalty : α → ℕ) {scale : ℝ} (hscale : 0 < scale)
    (base obs : α → ℝ)
    (hden :
      finiteFactorLimitDenominator s base
        (countHardFieldLimitFactor penalty) ≠ 0) :
    Tendsto
      (fun H : ℝ =>
        finiteFactorRatio s base obs (countHardFieldFactor penalty scale) H)
      atTop
      (𝓝
        (finiteFactorLimitRatio s base obs
          (countHardFieldLimitFactor penalty))) := by
  exact finiteFactorRatio_tendsto s base obs
    (countHardFieldLimitFactor penalty)
    (countHardFieldFactor penalty scale)
    (fun a _ha => countHardFieldFactor_tendsto penalty hscale a)
    hden


theorem countHardFieldLimitDenominator_pos_of_exists_pos {α : Type*}
    (s : Finset α) (penalty : α → ℕ) (base : α → ℝ)
    (hnonneg : ∀ a, a ∈ s → penalty a = 0 → 0 ≤ base a)
    (hpos : ∃ a, a ∈ s ∧ penalty a = 0 ∧ 0 < base a) :
    0 < finiteFactorLimitDenominator s base
      (countHardFieldLimitFactor penalty) := by
  classical
  unfold finiteFactorLimitDenominator countHardFieldLimitFactor
  refine Finset.sum_pos' ?_ ?_
  · intro a ha
    by_cases hzero : penalty a = 0
    · simpa [hzero] using hnonneg a ha hzero
    · simp [hzero]
  · obtain ⟨a, has, hzero, hbase⟩ := hpos
    refine ⟨a, has, ?_⟩
    simpa [hzero] using hbase


theorem countHardFieldLimitDenominator_ne_zero_of_exists_pos {α : Type*}
    (s : Finset α) (penalty : α → ℕ) (base : α → ℝ)
    (hnonneg : ∀ a, a ∈ s → penalty a = 0 → 0 ≤ base a)
    (hpos : ∃ a, a ∈ s ∧ penalty a = 0 ∧ 0 < base a) :
    finiteFactorLimitDenominator s base
      (countHardFieldLimitFactor penalty) ≠ 0 :=
  (countHardFieldLimitDenominator_pos_of_exists_pos
    s penalty base hnonneg hpos).ne'

end Exact3D
end StatMech
