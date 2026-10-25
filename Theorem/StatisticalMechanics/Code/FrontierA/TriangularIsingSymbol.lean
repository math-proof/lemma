/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingSymbol.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.RiemannPeriodic2D
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingSymbol
open scoped BigOperators
open MeasureTheory


namespace StatMech.FrontierA

theorem one_add_tanh_sq_mul_cosh_sq (x : ℝ) :
    (1 + Real.tanh x ^ 2) * Real.cosh x ^ 2 = Real.cosh (2 * x) := by
  rw [Real.tanh_eq_sinh_div_cosh, Real.cosh_two_mul]
  field_simp [(Real.cosh_pos x).ne']

theorem one_sub_tanh_sq_mul_cosh_sq (x : ℝ) :
    (1 - Real.tanh x ^ 2) * Real.cosh x ^ 2 = 1 := by
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp [(Real.cosh_pos x).ne']
  exact Real.cosh_sq_sub_sinh_sq x

theorem two_tanh_mul_cosh_sq (x : ℝ) :
    2 * Real.tanh x * Real.cosh x ^ 2 = Real.sinh (2 * x) := by
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_two_mul]
  field_simp [(Real.cosh_pos x).ne']


theorem triangularIsingHighTempSymbol_mul_cosh_sq
    (J1 J2 J3 k1 k2 : ℝ) :
    triangularIsingHighTempSymbol J1 J2 J3 k1 k2 *
        (Real.cosh J1 ^ 2 * Real.cosh J2 ^ 2 * Real.cosh J3 ^ 2) =
      triangularIsingSymbol J1 J2 J3 k1 k2 := by
  rw [triangularIsingHighTempSymbol, triangularIsingSymbol]
  have hplus1 := one_add_tanh_sq_mul_cosh_sq J1
  have hplus2 := one_add_tanh_sq_mul_cosh_sq J2
  have hplus3 := one_add_tanh_sq_mul_cosh_sq J3
  have hminus1 := one_sub_tanh_sq_mul_cosh_sq J1
  have hminus2 := one_sub_tanh_sq_mul_cosh_sq J2
  have hminus3 := one_sub_tanh_sq_mul_cosh_sq J3
  have htanh1 := two_tanh_mul_cosh_sq J1
  have htanh2 := two_tanh_mul_cosh_sq J2
  have htanh3 := two_tanh_mul_cosh_sq J3
  calc
    ((1 + Real.tanh J1 ^ 2) * (1 + Real.tanh J2 ^ 2) *
          (1 + Real.tanh J3 ^ 2) +
        8 * Real.tanh J1 * Real.tanh J2 * Real.tanh J3 -
        2 * (Real.tanh J1 * (1 - Real.tanh J2 ^ 2) *
              (1 - Real.tanh J3 ^ 2) * Real.cos k1 +
          Real.tanh J2 * (1 - Real.tanh J1 ^ 2) *
              (1 - Real.tanh J3 ^ 2) * Real.cos k2 +
          Real.tanh J3 * (1 - Real.tanh J1 ^ 2) *
              (1 - Real.tanh J2 ^ 2) * Real.cos (k1 + k2))) *
          (Real.cosh J1 ^ 2 * Real.cosh J2 ^ 2 * Real.cosh J3 ^ 2) =
        ((1 + Real.tanh J1 ^ 2) * Real.cosh J1 ^ 2) *
          ((1 + Real.tanh J2 ^ 2) * Real.cosh J2 ^ 2) *
          ((1 + Real.tanh J3 ^ 2) * Real.cosh J3 ^ 2) +
        (2 * Real.tanh J1 * Real.cosh J1 ^ 2) *
          (2 * Real.tanh J2 * Real.cosh J2 ^ 2) *
          (2 * Real.tanh J3 * Real.cosh J3 ^ 2) -
        ((2 * Real.tanh J1 * Real.cosh J1 ^ 2) *
            ((1 - Real.tanh J2 ^ 2) * Real.cosh J2 ^ 2) *
            ((1 - Real.tanh J3 ^ 2) * Real.cosh J3 ^ 2) * Real.cos k1 +
          (2 * Real.tanh J2 * Real.cosh J2 ^ 2) *
            ((1 - Real.tanh J1 ^ 2) * Real.cosh J1 ^ 2) *
            ((1 - Real.tanh J3 ^ 2) * Real.cosh J3 ^ 2) * Real.cos k2 +
          (2 * Real.tanh J3 * Real.cosh J3 ^ 2) *
            ((1 - Real.tanh J1 ^ 2) * Real.cosh J1 ^ 2) *
            ((1 - Real.tanh J2 ^ 2) * Real.cosh J2 ^ 2) *
              Real.cos (k1 + k2)) := by ring
    _ = _ := by
      rw [hplus1, hplus2, hplus3, hminus1, hminus2,
        hminus3, htanh1, htanh2, htanh3]
      ring


end StatMech.FrontierA
