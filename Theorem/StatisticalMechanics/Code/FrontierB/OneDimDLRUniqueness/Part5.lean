/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimDLRUniqueness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierB.OneDimFiniteVolumeBridge.Part18
import Theorem.StatisticalMechanics.Code.Ising.GibbsSimplexInfinite.Part3
import Def.StatisticalMechanics.Code.FrontierB.OneDimDLRUniqueness.Part6
open scoped BigOperators
open Finset Matrix


namespace StatMech.FrontierB

open StatMech.Lattice StatMech.Ising StatMech.FrontierC


theorem sum_fvWeight_block_eq_matrix_pow
    (eta : ConfigSpace (Site 1)) (r m : ℕ) (beta h : ℝ)
    (p : Fin (2 * r + 1) → Fin 2) :
    (∑ tau : {x // x ∈ box 1 (r + m)} → Bool,
      if glue eta tau ∈ blockStateEvent r p then
        fvWeight eta (r + m) (bondFinsetTouch 1 (r + m)) beta h tau else 0) =
      fvEndpointFactor eta (r + m) beta h *
        ((isingTransferReal beta (beta * h) ^ (m + 1))
            (fvLeftBoundaryState eta (r + m)) (p 0) *
          fixedWordProduct (isingTransferReal beta (beta * h)) p *
            (isingTransferReal beta (beta * h) ^ (m + 1))
              (p (Fin.last (2 * r))) (fvRightBoundaryState eta (r + m))) := by
  simp_rw [fvWeight_eq_endpointFactor_mul_openProduct]
  have hfactor :
      (∑ tau : {x // x ∈ box 1 (r + m)} → Bool,
        if glue eta tau ∈ blockStateEvent r p then
          fvEndpointFactor eta (r + m) beta h *
            fvTransferProduct eta (r + m) tau beta h else 0) =
        fvEndpointFactor eta (r + m) beta h *
          ∑ tau : {x // x ∈ box 1 (r + m)} → Bool,
            if glue eta tau ∈ blockStateEvent r p then
              fvTransferProduct eta (r + m) tau beta h else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro tau htau
    by_cases hp : glue eta tau ∈ blockStateEvent r p <;> simp [hp]
  rw [hfactor, sum_fvTransferProduct_block_eq_matrix_pow]

theorem fvBlockStateProb_eq_matrix_ratio
    (eta : ConfigSpace (Site 1)) (r m : ℕ) (beta h : ℝ)
    (p : Fin (2 * r + 1) → Fin 2) :
    fvBlockStateProb eta r m beta h p =
      ((isingTransferReal beta (beta * h) ^ (m + 1))
          (fvLeftBoundaryState eta (r + m)) (p 0) *
        fixedWordProduct (isingTransferReal beta (beta * h)) p *
          (isingTransferReal beta (beta * h) ^ (m + 1))
            (p (Fin.last (2 * r))) (fvRightBoundaryState eta (r + m))) /
      (isingTransferReal beta (beta * h) ^ (2 * (r + m) + 2))
        (fvLeftBoundaryState eta (r + m))
        (fvRightBoundaryState eta (r + m)) := by
  unfold fvBlockStateProb fvProb
  have hdiv :
      (∑ tau : {x // x ∈ box 1 (r + m)} → Bool,
        if glue eta tau ∈ blockStateEvent r p then
          fvWeight eta (r + m) (bondFinsetTouch 1 (r + m)) beta h tau /
            fvZ eta (r + m) (bondFinsetTouch 1 (r + m)) beta h else 0) =
        (∑ tau : {x // x ∈ box 1 (r + m)} → Bool,
          if glue eta tau ∈ blockStateEvent r p then
            fvWeight eta (r + m) (bondFinsetTouch 1 (r + m)) beta h tau else 0) /
          fvZ eta (r + m) (bondFinsetTouch 1 (r + m)) beta h := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro tau htau
    by_cases hp : glue eta tau ∈ blockStateEvent r p <;> simp [hp]
  rw [hdiv, sum_fvWeight_block_eq_matrix_pow,
    fvZ_eq_endpointFactor_mul_matrix_pow]
  apply mul_div_mul_left
  exact (Real.exp_pos _).ne'

theorem fvMeasure_blockStateEvent_real
    (eta : ConfigSpace (Site 1)) (r m : ℕ) (beta h : ℝ)
    (p : Fin (2 * r + 1) → Fin 2) :
    (fvMeasure eta (r + m) (bondFinsetTouch 1 (r + m)) beta h).real
        (blockStateEvent r p) = fvBlockStateProb eta r m beta h p := by
  rw [fvMeasure_real_eq eta (r + m) (bondFinsetTouch 1 (r + m)) beta h
    (measurableSet_blockStateEvent r p)]
  unfold fvBlockStateProb
  apply Finset.sum_congr rfl
  intro tau htau
  by_cases hp : glue eta tau ∈ blockStateEvent r p
  · rw [if_pos hp]
    simp [Set.indicator_of_mem hp]
  · rw [if_neg hp]
    simp [Set.indicator_of_notMem hp]


lemma isingTransferProjectorPlus_cross_general (beta h : ℝ) (a c d b : Fin 2) :
    isingTransferProjectorPlus beta h a c *
        isingTransferProjectorPlus beta h d b =
      isingTransferProjectorPlus beta h a b *
        isingTransferProjectorPlus beta h d c := by
  have hd := isingTransferProjectorPlus_det beta h
  rw [Matrix.det_fin_two] at hd
  fin_cases a <;> fin_cases c <;> fin_cases d <;> fin_cases b <;>
    simp_all <;> ring_nf at * <;> nlinarith

theorem isingTransfer_fixedWord_weight_tendsto
    (beta h : ℝ) (k : ℕ) (p : Fin (k + 1) → Fin 2) (a b : Fin 2) :
    Filter.Tendsto
      (fun m : ℕ =>
        (isingTransferReal beta h ^ (m + 1)) a (p 0) *
          fixedWordProduct (isingTransferReal beta h) p *
            (isingTransferReal beta h ^ (m + 1)) (p (Fin.last k)) b /
          (isingTransferReal beta h ^ (2 * (m + 1) + k)) a b)
      Filter.atTop
      (nhds (isingTransferProjectorPlus beta h (p (Fin.last k)) (p 0) *
        fixedWordProduct (isingTransferReal beta h) p *
          (isingTransferEigenPlus beta h)⁻¹ ^ k)) := by
  let c : ℝ := (isingTransferEigenPlus beta h)⁻¹
  let A := isingTransferReal beta h
  let P := isingTransferProjectorPlus beta h
  let W := fixedWordProduct A p
  have hc : c ≠ 0 := inv_ne_zero (isingTransfer_eigenPlus_pos beta h).ne'
  have hshift : Filter.Tendsto (fun m : ℕ => m + 1) Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop]
    intro N
    filter_upwards [Filter.eventually_ge_atTop N] with m hm
    omega
  have hdenShift : Filter.Tendsto (fun m : ℕ => 2 * (m + 1) + k)
      Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop]
    intro N
    filter_upwards [Filter.eventually_ge_atTop N] with m hm
    omega
  have hleft := (isingTransfer_normalized_entry_tendsto beta h a (p 0)).comp hshift
  have hright :=
    (isingTransfer_normalized_entry_tendsto beta h (p (Fin.last k)) b).comp hshift
  have hden := (isingTransfer_normalized_entry_tendsto beta h a b).comp hdenShift
  have hleft' : Filter.Tendsto
      (fun m : ℕ => (c ^ (m + 1) • A ^ (m + 1)) a (p 0))
      Filter.atTop (nhds (P a (p 0))) := by
    simpa only [Function.comp_apply, c, A, P] using hleft
  have hright' : Filter.Tendsto
      (fun m : ℕ => (c ^ (m + 1) • A ^ (m + 1)) (p (Fin.last k)) b)
      Filter.atTop (nhds (P (p (Fin.last k)) b)) := by
    simpa only [Function.comp_apply, c, A, P] using hright
  have hden' : Filter.Tendsto
      (fun m : ℕ => (c ^ (2 * (m + 1) + k) • A ^ (2 * (m + 1) + k)) a b)
      Filter.atTop (nhds (P a b)) := by
    simpa only [Function.comp_apply, c, A, P] using hden
  have hratio := ((hleft'.mul hright').mul_const W).div hden'
    (ne_of_gt (isingTransferProjectorPlus_pos beta h a b))
  have hscaled := hratio.mul_const (c ^ k)
  have hlimit :
      (P a (p 0) * P (p (Fin.last k)) b * W / P a b) * c ^ k =
        P (p (Fin.last k)) (p 0) * W * c ^ k := by
    have hpab : P a b ≠ 0 := ne_of_gt (isingTransferProjectorPlus_pos beta h a b)
    rw [show P a (p 0) * P (p (Fin.last k)) b =
      P a b * P (p (Fin.last k)) (p 0) by
        exact isingTransferProjectorPlus_cross_general beta h a (p 0)
          (p (Fin.last k)) b]
    rw [show P a b * P (p (Fin.last k)) (p 0) * W =
      P a b * (P (p (Fin.last k)) (p 0) * W) by ring]
    rw [mul_div_cancel_left₀ _ hpab]
  rw [hlimit] at hscaled
  simpa only [c, A, P, W] using hscaled.congr' (Filter.Eventually.of_forall (fun m => by
    simp only [Pi.div_apply, Matrix.smul_apply, smul_eq_mul]
    have hpow : c ^ (2 * (m + 1) + k) = (c ^ (m + 1)) ^ 2 * c ^ k := by
      rw [pow_add, show 2 * (m + 1) = (m + 1) * 2 by omega, pow_mul, pow_two]
    rw [hpow]
    field_simp
    ring))

end StatMech.FrontierB
