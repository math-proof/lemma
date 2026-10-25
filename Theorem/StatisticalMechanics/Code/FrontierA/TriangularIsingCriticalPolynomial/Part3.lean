/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalPolynomial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingSymbol.Part2
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalPolynomial.Part3


namespace StatMech.FrontierA

theorem criticalRate_sub_one_factor
    {t r : ℝ} (ht : 1 - t ^ 2 ≠ 0) (hr : 1 - r ^ 2 ≠ 0) :
    (2 * t / (1 - t ^ 2)) ^ 2 +
          2 * (2 * t / (1 - t ^ 2)) * (2 * r / (1 - r ^ 2)) - 1 =
      -triangularIsingCriticalPolynomial t r *
          triangularIsingCriticalCompanion t r /
        ((1 - t ^ 2) ^ 2 * (1 - r ^ 2)) := by
  unfold triangularIsingCriticalPolynomial triangularIsingCriticalCompanion
  field_simp [ht, hr]
  ring


end StatMech.FrontierA
