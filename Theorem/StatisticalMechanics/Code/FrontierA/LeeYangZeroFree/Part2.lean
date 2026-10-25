/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangZeroFree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangAsano.Part15
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.LogDeriv
import Def.StatisticalMechanics.Code.FrontierA.LeeYangZeroFree.Part2
open scoped BigOperators
open Finset Polynomial


namespace StatMech.FrontierA

open StatMech.Ising StatMech.FrontierB

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


theorem leeYangFugacityLogDerivative_eq_logDeriv (beta : ℝ) (z : ℂ) :
    leeYangFugacityLogDerivative G beta z =
      logDeriv (fun w ↦ (leeYangComplexPolynomial G beta).eval w) z := by
  rw [logDeriv_apply]
  unfold leeYangFugacityLogDerivative
  rw [(leeYangComplexPolynomial G beta).hasDerivAt z |>.deriv]

theorem leeYangFugacityLogDerivative_analyticOnNhd_offCircle
    {beta : ℝ} (hbeta : 0 ≤ beta) :
    AnalyticOnNhd ℂ (leeYangFugacityLogDerivative G beta)
      {z : ℂ | ‖z‖ ≠ 1} := by
  have hnum : AnalyticOnNhd ℂ
      (fun z ↦ (leeYangComplexPolynomial G beta).derivative.eval z) Set.univ :=
    AnalyticOnNhd.eval_polynomial _
  have hden : AnalyticOnNhd ℂ
      (fun z ↦ (leeYangComplexPolynomial G beta).eval z) Set.univ :=
    AnalyticOnNhd.eval_polynomial _
  exact (hnum.mono (Set.subset_univ _)).div (hden.mono (Set.subset_univ _))
    (fun z hz ↦ leeYangComplexPolynomial_ne_zero_of_norm_ne_one G hbeta hz)

theorem leeYangFugacityLogDerivative_analyticOnNhd_openUnitDisk
    {beta : ℝ} (hbeta : 0 ≤ beta) :
    AnalyticOnNhd ℂ (leeYangFugacityLogDerivative G beta)
      {z : ℂ | ‖z‖ < 1} := by
  apply (leeYangFugacityLogDerivative_analyticOnNhd_offCircle G hbeta).mono
  intro z hz
  exact ne_of_lt hz

theorem leeYangFugacityLogDerivative_analyticOnNhd_exterior
    {beta : ℝ} (hbeta : 0 ≤ beta) :
    AnalyticOnNhd ℂ (leeYangFugacityLogDerivative G beta)
      {z : ℂ | 1 < ‖z‖} := by
  apply (leeYangFugacityLogDerivative_analyticOnNhd_offCircle G hbeta).mono
  intro z hz
  exact ne_of_gt hz

end StatMech.FrontierA
