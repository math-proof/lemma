/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSymbolReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingSymbol.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterLocal.Part2


namespace StatMech.FrontierA

theorem sinh_neg_log_eq {x : Real} (hx : 0 < x) :
    Real.sinh (-Real.log x) = (1 - x ^ 2) / (2 * x) := by
  rw [Real.sinh_eq, Real.exp_neg, neg_neg, Real.exp_log hx]
  field_simp [hx.ne']

theorem cosh_neg_log_eq {x : Real} (hx : 0 < x) :
    Real.cosh (-Real.log x) = (1 + x ^ 2) / (2 * x) := by
  rw [Real.cosh_eq, Real.exp_neg, neg_neg, Real.exp_log hx]
  field_simp [hx.ne']

theorem cosh_div_sinh_neg_log {x : Real} (hx : 0 < x) (hx1 : x < 1) :
    Real.cosh (-Real.log x) / Real.sinh (-Real.log x) =
      (1 + x ^ 2) / (1 - x ^ 2) := by
  rw [sinh_neg_log_eq hx, cosh_neg_log_eq hx]
  have hden : 1 - x ^ 2 ≠ 0 := by nlinarith
  field_simp [hx.ne', hden]

theorem one_div_sinh_neg_log {x : Real} (hx : 0 < x) (hx1 : x < 1) :
    1 / Real.sinh (-Real.log x) = 2 * x / (1 - x ^ 2) := by
  rw [sinh_neg_log_eq hx]
  have hden : 1 - x ^ 2 ≠ 0 := by nlinarith
  field_simp [hx.ne', hden]

theorem reduced_symbol_algebra
    (t x k q : Real) (hx : 0 < x) (hx1 : x < 1) :
    (Real.cosh t * Real.cosh (-Real.log x) -
        (Real.sinh t * (-Real.cos k) +
          Real.sinh (-Real.log x) * Real.cos q)) /
        Real.sinh (-Real.log x) =
      Real.cosh t * ((1 + x ^ 2) / (1 - x ^ 2)) +
        Real.sinh t * (2 * x / (1 - x ^ 2)) * Real.cos k -
        Real.cos q := by
  rw [sinh_neg_log_eq hx, cosh_neg_log_eq hx]
  have hden : 1 - x ^ 2 ≠ 0 := by nlinarith
  field_simp [hx.ne', hden]
  ring

end StatMech.FrontierA
