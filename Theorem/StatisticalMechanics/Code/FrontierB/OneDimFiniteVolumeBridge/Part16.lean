/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.OneDimTransferPerron
import Theorem.StatisticalMechanics.Code.Ising.FVConsistencyProve.Part2
import Theorem.StatisticalMechanics.Code.Lattice.ContourCountInjection.Part2
import Def.StatisticalMechanics.Code.FrontierB.OneDimFiniteVolumeBridge.Part16
open scoped BigOperators
open Finset Matrix


namespace StatMech.FrontierB

open StatMech.Lattice StatMech.Ising StatMech.FrontierC


theorem sum_fvWeight_center_eq_matrix_pow
    (eta : ConfigSpace (Site 1)) (n : ℕ) (beta h : ℝ) (s : Fin 2) :
    (∑ tau : {x // x ∈ box 1 n} → Bool,
      if fvPathState eta n tau (n + 1) = s then
        fvWeight eta n (bondFinsetTouch 1 n) beta h tau else 0) =
      fvEndpointFactor eta n beta h *
        ((isingTransferReal beta (beta * h) ^ (n + 1))
            (fvLeftBoundaryState eta n) s *
          (isingTransferReal beta (beta * h) ^ (n + 1))
            s (fvRightBoundaryState eta n)) := by
  simp_rw [fvWeight_eq_endpointFactor_mul_openProduct]
  have hfactor :
      (∑ tau : {x // x ∈ box 1 n} → Bool,
        if fvPathState eta n tau (n + 1) = s then
          fvEndpointFactor eta n beta h * fvTransferProduct eta n tau beta h else 0) =
        fvEndpointFactor eta n beta h *
          ∑ tau : {x // x ∈ box 1 n} → Bool,
            if fvPathState eta n tau (n + 1) = s then
              fvTransferProduct eta n tau beta h else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro tau htau
    by_cases hc : fvPathState eta n tau (n + 1) = s <;> simp [hc]
  rw [hfactor, sum_fvTransferProduct_center_eq_matrix_pow]

theorem fvCenterStateProb_eq_matrix_ratio
    (eta : ConfigSpace (Site 1)) (n : ℕ) (beta h : ℝ) (s : Fin 2) :
    fvCenterStateProb eta n beta h s =
      ((isingTransferReal beta (beta * h) ^ (n + 1))
          (fvLeftBoundaryState eta n) s *
        (isingTransferReal beta (beta * h) ^ (n + 1))
          s (fvRightBoundaryState eta n)) /
      (isingTransferReal beta (beta * h) ^ (2 * n + 2))
        (fvLeftBoundaryState eta n) (fvRightBoundaryState eta n) := by
  unfold fvCenterStateProb fvProb
  have hdiv :
      (∑ tau : {x // x ∈ box 1 n} → Bool,
        if fvPathState eta n tau (n + 1) = s then
          fvWeight eta n (bondFinsetTouch 1 n) beta h tau /
            fvZ eta n (bondFinsetTouch 1 n) beta h else 0) =
        (∑ tau : {x // x ∈ box 1 n} → Bool,
          if fvPathState eta n tau (n + 1) = s then
            fvWeight eta n (bondFinsetTouch 1 n) beta h tau else 0) /
              fvZ eta n (bondFinsetTouch 1 n) beta h := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro tau htau
    by_cases hc : fvPathState eta n tau (n + 1) = s <;> simp [hc]
  rw [hdiv]
  have hsum :
      (∑ tau : {x // x ∈ box 1 n} → Bool,
        (if fvPathState eta n tau (n + 1) = s then
          fvWeight eta n (bondFinsetTouch 1 n) beta h tau else 0)) =
        fvEndpointFactor eta n beta h *
          ((isingTransferReal beta (beta * h) ^ (n + 1))
              (fvLeftBoundaryState eta n) s *
            (isingTransferReal beta (beta * h) ^ (n + 1))
              s (fvRightBoundaryState eta n)) :=
    sum_fvWeight_center_eq_matrix_pow eta n beta h s
  rw [hsum, fvZ_eq_endpointFactor_mul_matrix_pow]
  apply mul_div_mul_left
  exact (Real.exp_pos _).ne'

theorem fvCenterStateProb_tendsto
    (eta : ℕ → ConfigSpace (Site 1)) (beta h : ℝ) (s : Fin 2) :
    Filter.Tendsto
      (fun n => fvCenterStateProb (eta n) n beta h s)
      Filter.atTop (nhds (isingTransferProjectorPlus beta (beta * h) s s)) := by
  have hshift : Filter.Tendsto (fun n : ℕ => n + 1) Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop]
    intro N
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    omega
  have hfixed (a b : Fin 2) : Filter.Tendsto
      (fun n : ℕ =>
        (isingTransferReal beta (beta * h) ^ (n + 1)) a s *
          (isingTransferReal beta (beta * h) ^ (n + 1)) s b /
            (isingTransferReal beta (beta * h) ^ (2 * n + 2)) a b)
      Filter.atTop (nhds (isingTransferProjectorPlus beta (beta * h) s s)) := by
    have ht := (isingTransfer_central_state_weight_tendsto beta (beta * h) a s b).comp hshift
    simpa only [Function.comp_apply, show ∀ n : ℕ, 2 * (n + 1) = 2 * n + 2 by omega]
      using ht
  rw [Metric.tendsto_atTop]
  intro eps heps
  obtain ⟨N00, h00⟩ := (Metric.tendsto_atTop.mp (hfixed 0 0)) eps heps
  obtain ⟨N01, h01⟩ := (Metric.tendsto_atTop.mp (hfixed 0 1)) eps heps
  obtain ⟨N10, h10⟩ := (Metric.tendsto_atTop.mp (hfixed 1 0)) eps heps
  obtain ⟨N11, h11⟩ := (Metric.tendsto_atTop.mp (hfixed 1 1)) eps heps
  refine ⟨max (max N00 N01) (max N10 N11), fun n hn => ?_⟩
  rw [fvCenterStateProb_eq_matrix_ratio]
  have hn00 : N00 ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hn)
  have hn01 : N01 ≤ n := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hn)
  have hn10 : N10 ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hn)
  have hn11 : N11 ≤ n := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hn)
  generalize hL : fvLeftBoundaryState (eta n) n = L
  generalize hR : fvRightBoundaryState (eta n) n = R
  fin_cases L <;> fin_cases R
  · simpa only [hL, hR] using h00 n hn00
  · simpa only [hL, hR] using h01 n hn01
  · simpa only [hL, hR] using h10 n hn10
  · simpa only [hL, hR] using h11 n hn11


end StatMech.FrontierB
