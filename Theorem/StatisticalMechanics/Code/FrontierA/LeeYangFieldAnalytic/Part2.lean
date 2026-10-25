/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangFieldAnalytic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangZeroFree.Part2
import Def.StatisticalMechanics.Code.FrontierA.LeeYangFieldAnalytic.Part2
open scoped BigOperators
open Finset


namespace StatMech.FrontierA

open StatMech.Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

theorem leeYangComplexFieldLogDerivative_eq_logDeriv
    (beta : ℝ) (h : ℂ) :
    leeYangComplexFieldLogDerivative G beta h =
      logDeriv (leeYangComplexFieldPartition G beta) h := by
  rw [logDeriv_apply]
  unfold leeYangComplexFieldLogDerivative
  rw [leeYangComplexFieldMagnetizationNumerator_eq_deriv]

theorem leeYangComplexFieldLogDerivative_ofReal
    (beta h : ℝ) :
    leeYangComplexFieldLogDerivative G beta (h : ℂ) =
      (beta : ℂ) *
        (isingExpectation G beta h (fun s => ∑ v : V, spin s v) : ℂ) := by
  rw [leeYangComplexFieldLogDerivative, leeYangComplexFieldPartition_ofReal,
    leeYangComplexFieldMagnetizationNumerator_ofReal]
  have hreal :
      (beta * ∑ s : ConfigSpace V,
          (∑ v : V, spin s v) * isingWeight G beta h s) /
          isingZ G beta h =
        beta * isingExpectation G beta h (fun s => ∑ v : V, spin s v) := by
    unfold isingExpectation isingProb
    calc
      (beta * ∑ s : ConfigSpace V,
          (∑ v : V, spin s v) * isingWeight G beta h s) /
          isingZ G beta h =
          ∑ s : ConfigSpace V,
            beta * ((∑ v : V, spin s v) * isingWeight G beta h s) /
              isingZ G beta h := by
        rw [Finset.mul_sum, Finset.sum_div]
      _ = ∑ s : ConfigSpace V,
          beta * (isingWeight G beta h s / isingZ G beta h) *
            (∑ v : V, spin s v) := by
        apply Finset.sum_congr rfl
        intro s hs
        ring
      _ = beta * ∑ s : ConfigSpace V,
          isingWeight G beta h s / isingZ G beta h *
            (∑ v : V, spin s v) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s hs
        ring
  exact_mod_cast hreal

theorem leeYangComplexFieldLogDerivative_analyticOnNhd_re_ne_zero
    {beta : ℝ} (hbeta : 0 ≤ beta) :
    AnalyticOnNhd ℂ (leeYangComplexFieldLogDerivative G beta)
      {h : ℂ | h.re ≠ 0} := by
  have hden := (leeYangComplexFieldPartition_analyticOnNhd G beta).mono
    (Set.subset_univ {h : ℂ | h.re ≠ 0})
  have hnum : AnalyticOnNhd ℂ
      (leeYangComplexFieldMagnetizationNumerator G beta)
      {h : ℂ | h.re ≠ 0} := by
    rw [show leeYangComplexFieldMagnetizationNumerator G beta =
        deriv (leeYangComplexFieldPartition G beta) by
      funext h
      exact leeYangComplexFieldMagnetizationNumerator_eq_deriv G beta h]
    exact (leeYangComplexFieldPartition_analyticOnNhd G beta).deriv.mono
      (Set.subset_univ _)
  exact hnum.div hden fun h hh =>
    leeYangComplexFieldPartition_ne_zero_of_nonneg_re_ne_zero G hbeta hh

theorem leeYangComplexFieldLogDerivative_analyticOnNhd_rightHalfPlane
    {beta : ℝ} (hbeta : 0 ≤ beta) :
    AnalyticOnNhd ℂ (leeYangComplexFieldLogDerivative G beta)
      {h : ℂ | 0 < h.re} := by
  apply (leeYangComplexFieldLogDerivative_analyticOnNhd_re_ne_zero G hbeta).mono
  intro h hh
  exact ne_of_gt hh

theorem leeYangComplexFieldLogDerivative_analyticOnNhd_leftHalfPlane
    {beta : ℝ} (hbeta : 0 ≤ beta) :
    AnalyticOnNhd ℂ (leeYangComplexFieldLogDerivative G beta)
      {h : ℂ | h.re < 0} := by
  apply (leeYangComplexFieldLogDerivative_analyticOnNhd_re_ne_zero G hbeta).mono
  intro h hh
  exact ne_of_lt hh

end StatMech.FrontierA
