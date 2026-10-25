/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalEvalAlgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalSeries.Part6
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Def.StatisticalMechanics.Code.Onsager.DecorationFormalEvalAlgebra.Part2


namespace StatMech.Onsager

open BigOperators Finset

theorem ons_MvSeriesEvalSummable.mul
    {E : Type*} [DecidableEq E]
    {f g : MvPowerSeries E ℂ} {weight : E → ℂ}
    (hf : ons_MvSeriesEvalSummable f weight)
    (hg : ons_MvSeriesEvalSummable g weight) :
    ons_MvSeriesEvalSummable (f * g) weight := by
  let F := fun m : E →₀ ℕ ↦
    ‖MvPowerSeries.coeff m f * ons_mvMonomialValue weight m‖
  let G := fun m : E →₀ ℕ ↦
    ‖MvPowerSeries.coeff m g * ons_mvMonomialValue weight m‖
  have hF : Summable F := hf
  have hG : Summable G := hg
  have hFnorm : Summable fun m ↦ ‖F m‖ := by
    simpa [F, Real.norm_eq_abs, abs_of_nonneg] using hF
  have hGnorm : Summable fun m ↦ ‖G m‖ := by
    simpa [G, Real.norm_eq_abs, abs_of_nonneg] using hG
  have hprod : Summable fun p : (E →₀ ℕ) × (E →₀ ℕ) ↦
      F p.1 * G p.2 :=
    summable_mul_of_summable_norm hFnorm hGnorm
  have hmajor : Summable fun m : E →₀ ℕ ↦
      ∑ p ∈ Finset.antidiagonal m, F p.1 * G p.2 :=
    summable_sum_mul_antidiagonal_of_summable_mul hprod
  apply Summable.of_nonneg_of_le
    (fun m ↦ norm_nonneg _)
    (fun m ↦ ?_) hmajor
  rw [MvPowerSeries.coeff_mul, Finset.sum_mul]
  calc
    ‖∑ p ∈ Finset.antidiagonal m,
        (MvPowerSeries.coeff p.1 f * MvPowerSeries.coeff p.2 g) *
          ons_mvMonomialValue weight m‖ ≤
        ∑ p ∈ Finset.antidiagonal m,
          ‖(MvPowerSeries.coeff p.1 f * MvPowerSeries.coeff p.2 g) *
            ons_mvMonomialValue weight m‖ :=
      norm_sum_le _ _
    _ = ∑ p ∈ Finset.antidiagonal m, F p.1 * G p.2 := by
      apply Finset.sum_congr rfl
      intro p hp
      have hadd : p.1 + p.2 = m :=
        Finset.mem_antidiagonal.mp hp
      rw [← hadd, ons_mvMonomialValue_add]
      simp only [F, G, norm_mul]
      ring

theorem ons_mvSeriesEval_mul
    {E : Type*} [DecidableEq E]
    {f g : MvPowerSeries E ℂ} {weight : E → ℂ}
    (hf : ons_MvSeriesEvalSummable f weight)
    (hg : ons_MvSeriesEvalSummable g weight) :
    ons_mvSeriesEval (f * g) weight =
      ons_mvSeriesEval f weight * ons_mvSeriesEval g weight := by
  let F := fun m : E →₀ ℕ ↦
    MvPowerSeries.coeff m f * ons_mvMonomialValue weight m
  let G := fun m : E →₀ ℕ ↦
    MvPowerSeries.coeff m g * ons_mvMonomialValue weight m
  have hF : Summable F := Summable.of_norm hf
  have hG : Summable G := Summable.of_norm hg
  have hFnorm : Summable fun m ↦ ‖F m‖ := hf
  have hGnorm : Summable fun m ↦ ‖G m‖ := hg
  have hprod : Summable fun p : (E →₀ ℕ) × (E →₀ ℕ) ↦
      F p.1 * G p.2 :=
    summable_mul_of_summable_norm hFnorm hGnorm
  rw [ons_mvSeriesEval_eq, ons_mvSeriesEval_eq, ons_mvSeriesEval_eq,
    hF.tsum_mul_tsum_eq_tsum_sum_antidiagonal hG hprod]
  apply tsum_congr
  intro m
  rw [MvPowerSeries.coeff_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hadd : p.1 + p.2 = m := Finset.mem_antidiagonal.mp hp
  rw [← hadd, ons_mvMonomialValue_add]
  simp only [F, G]
  ring

end StatMech.Onsager
