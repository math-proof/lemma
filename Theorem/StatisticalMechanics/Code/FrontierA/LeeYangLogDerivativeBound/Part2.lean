/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangLogDerivativeBound.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangFieldAnalytic.Part3
import Mathlib.Algebra.Polynomial.Splits
import Def.StatisticalMechanics.Code.FrontierA.LeeYangLogDerivativeBound
open scoped BigOperators
open Polynomial


namespace StatMech.FrontierA

open StatMech.Ising StatMech.FrontierB StatMech.FrontierC

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

theorem leeYangNormalizedFieldLogDerivative_analyticOnNhd_re_ne_zero
    {beta : ℝ} (hbeta : 0 ≤ beta) :
    AnalyticOnNhd ℂ (leeYangNormalizedFieldLogDerivative G beta)
      {h : ℂ | h.re ≠ 0} := by
  exact (leeYangComplexFieldLogDerivative_analyticOnNhd_re_ne_zero
    G hbeta).div_const

theorem leeYangNormalizedFieldLogDerivative_ofReal
    (beta h : ℝ) :
    leeYangNormalizedFieldLogDerivative G beta (h : ℂ) =
      (beta : ℂ) *
        (isingExpectation G beta h (fun s => ∑ v : V, spin s v) : ℂ) /
          Fintype.card V := by
  rw [leeYangNormalizedFieldLogDerivative,
    leeYangComplexFieldLogDerivative_ofReal]

theorem leeYangNormalizedFieldLogDerivative_norm_le_rightHalfPlane
    [Nonempty V] {beta : ℝ} (hbeta : 0 < beta) {h : ℂ} (hh : 0 < h.re) :
    ‖leeYangNormalizedFieldLogDerivative G beta h‖ ≤
      beta + 2 * beta * ‖Complex.exp (-2 * (beta : ℂ) * h)‖ /
        (1 - ‖Complex.exp (-2 * (beta : ℂ) * h)‖) := by
  have hraw := leeYangComplexFieldLogDerivative_norm_le_rightHalfPlane G hbeta hh
  unfold leeYangNormalizedFieldLogDerivative
  rw [norm_div, Complex.norm_natCast]
  apply (div_le_iff₀ (by exact_mod_cast Fintype.card_pos :
    (0 : ℝ) < Fintype.card V)).2
  simpa only [mul_comm] using hraw

theorem leeYangNormalizedFieldLogDerivative_norm_le_leftHalfPlane
    [Nonempty V] {beta : ℝ} (hbeta : 0 < beta) {h : ℂ} (hh : h.re < 0) :
    ‖leeYangNormalizedFieldLogDerivative G beta h‖ ≤
      beta + 2 * beta * ‖Complex.exp (-2 * (beta : ℂ) * h)‖ /
        (‖Complex.exp (-2 * (beta : ℂ) * h)‖ - 1) := by
  have hraw := leeYangComplexFieldLogDerivative_norm_le_leftHalfPlane G hbeta hh
  unfold leeYangNormalizedFieldLogDerivative
  rw [norm_div, Complex.norm_natCast]
  apply (div_le_iff₀ (by exact_mod_cast Fintype.card_pos :
    (0 : ℝ) < Fintype.card V)).2
  simpa only [mul_comm] using hraw

end StatMech.FrontierA
