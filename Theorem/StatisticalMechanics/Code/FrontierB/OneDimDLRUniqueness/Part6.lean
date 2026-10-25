/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimDLRUniqueness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierB.OneDimFiniteVolumeBridge.Part18
import Theorem.StatisticalMechanics.Code.Ising.GibbsSimplexInfinite.Part3
import Def.StatisticalMechanics.Code.FrontierB.OneDimDLRUniqueness.Part7
open scoped BigOperators
open Finset Matrix


namespace StatMech.FrontierB

open StatMech.Lattice StatMech.Ising StatMech.FrontierC


theorem fvBlockStateProb_tendsto
    (eta : ℕ → ConfigSpace (Site 1)) (r : ℕ) (beta h : ℝ)
    (p : Fin (2 * r + 1) → Fin 2) :
    Filter.Tendsto (fun m => fvBlockStateProb (eta m) r m beta h p)
      Filter.atTop (nhds (blockStateLimit r beta h p)) := by
  have hfixed (a b : Fin 2) : Filter.Tendsto
      (fun m : ℕ =>
        (isingTransferReal beta (beta * h) ^ (m + 1)) a (p 0) *
          fixedWordProduct (isingTransferReal beta (beta * h)) p *
            (isingTransferReal beta (beta * h) ^ (m + 1))
              (p (Fin.last (2 * r))) b /
          (isingTransferReal beta (beta * h) ^ (2 * (r + m) + 2)) a b)
      Filter.atTop (nhds (blockStateLimit r beta h p)) := by
    simpa only [blockStateLimit, show ∀ m : ℕ,
      2 * (r + m) + 2 = 2 * (m + 1) + 2 * r by omega] using
      isingTransfer_fixedWord_weight_tendsto beta (beta * h) (2 * r) p a b
  rw [Metric.tendsto_atTop]
  intro eps heps
  obtain ⟨N00, h00⟩ := (Metric.tendsto_atTop.mp (hfixed 0 0)) eps heps
  obtain ⟨N01, h01⟩ := (Metric.tendsto_atTop.mp (hfixed 0 1)) eps heps
  obtain ⟨N10, h10⟩ := (Metric.tendsto_atTop.mp (hfixed 1 0)) eps heps
  obtain ⟨N11, h11⟩ := (Metric.tendsto_atTop.mp (hfixed 1 1)) eps heps
  refine ⟨max (max N00 N01) (max N10 N11), fun m hm => ?_⟩
  rw [fvBlockStateProb_eq_matrix_ratio]
  have hm00 : N00 ≤ m := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hm)
  have hm01 : N01 ≤ m := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hm)
  have hm10 : N10 ≤ m := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hm)
  have hm11 : N11 ≤ m := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hm)
  generalize hL : fvLeftBoundaryState (eta m) (r + m) = L
  generalize hR : fvRightBoundaryState (eta m) (r + m) = R
  fin_cases L <;> fin_cases R
  · simpa only [hL, hR] using h00 m hm00
  · simpa only [hL, hR] using h01 m hm01
  · simpa only [hL, hR] using h10 m hm10
  · simpa only [hL, hR] using h11 m hm11

theorem fvMeasure_blockStateEvent_tendsto
    (eta : ℕ → ConfigSpace (Site 1)) (r : ℕ) (beta h : ℝ)
    (p : Fin (2 * r + 1) → Fin 2) :
    Filter.Tendsto
      (fun m => (fvMeasure (eta m) (r + m) (bondFinsetTouch 1 (r + m)) beta h).real
        (blockStateEvent r p))
      Filter.atTop (nhds (blockStateLimit r beta h p)) := by
  simpa only [fvMeasure_blockStateEvent_real] using
    fvBlockStateProb_tendsto eta r beta h p


open MeasureTheory Filter

theorem dlr_blockStateEvent_real_eq_limit
    (beta h : ℝ) (mu : Measure (ConfigSpace (Site 1))) [IsProbabilityMeasure mu]
    (hmu : IsDLRState 1 beta h mu) (r : ℕ)
    (p : Fin (2 * r + 1) → Fin 2) :
    mu.real (blockStateEvent r p) = blockStateLimit r beta h p := by
  let F : ℕ → ConfigSpace (Site 1) → ℝ := fun m eta =>
    (fvMeasure eta (r + m) (bondFinsetTouch 1 (r + m)) beta h).real
      (blockStateEvent r p)
  have hmeas (m : ℕ) : AEStronglyMeasurable (F m) mu :=
    (fvMeasure_real_integrable beta h mu (r + m) _
      (measurableSet_blockStateEvent r p)).aestronglyMeasurable
  have hbound (m : ℕ) : ∀ᵐ eta ∂mu, ‖F m eta‖ ≤ (1 : ℝ) := by
    filter_upwards with eta
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one
  have hlim : ∀ᵐ eta ∂mu,
      Tendsto (fun m => F m eta) atTop (nhds (blockStateLimit r beta h p)) := by
    filter_upwards with eta
    exact fvMeasure_blockStateEvent_tendsto (fun _ => eta) r beta h p
  have hdct := tendsto_integral_of_dominated_convergence
    (fun _ : ConfigSpace (Site 1) => (1 : ℝ)) hmeas (integrable_const 1) hbound hlim
  have hintegral (m : ℕ) : ∫ eta, F m eta ∂mu = mu.real (blockStateEvent r p) := by
    rw [gsi_dlr_real_eq_integral beta h mu hmu (r + m)
      (measurableSet_blockStateEvent r p)]
  have hconst : Tendsto (fun _ : ℕ => mu.real (blockStateEvent r p)) atTop
      (nhds (mu.real (blockStateEvent r p))) := tendsto_const_nhds
  have hdct' : Tendsto (fun _ : ℕ => mu.real (blockStateEvent r p)) atTop
      (nhds (blockStateLimit r beta h p)) := by
    simpa only [F, hintegral, integral_const, probReal_univ, smul_eq_mul, one_mul]
      using hdct
  exact tendsto_nhds_unique hconst hdct'


end StatMech.FrontierB
