/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexParityBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSupportLexCounterexample.Part2
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Def.StatisticalMechanics.Code.Sharpness.BackboneSupportLexParityBridge.Part7
open Finset


namespace StatMech.Sharpness

theorem shbK4DirectRhoSeries_eq_polynomial
    (E : Finset shbK4Edge) (x : ℝ) :
    shbK4DirectRhoSeries E x =
      shbK4DirectRhoPolynomial E (Real.tanh x) := by
  rw [shbK4DirectRhoSeries, shbK4DirectFiberSeriesMass_eq,
    shbK4VacuumSeriesMass_eq, shbK4DirectRhoPolynomial]
  exact mul_div_mul_left _ _ (pow_ne_zero _ (Real.cosh_pos x).ne')


theorem shb_supportLex_series_P3_counterexample :
    shbK4DirectRhoSeries shbK4H (Real.artanh (2 / 3)) <
      shbK4DirectRhoSeries shbK4G (Real.artanh (2 / 3)) := by
  rw [shbK4DirectRhoSeries_eq_polynomial,
    shbK4DirectRhoSeries_eq_polynomial, shb_tanh_artanh_two_thirds]
  exact shb_supportLex_realParity_P3_counterexample

end StatMech.Sharpness
