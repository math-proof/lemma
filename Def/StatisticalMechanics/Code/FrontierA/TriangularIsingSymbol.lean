/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingSymbol.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.RiemannPeriodic2D
open scoped BigOperators
open MeasureTheory


namespace StatMech.FrontierA

noncomputable def triangularIsingSymbol
    (J1 J2 J3 k1 k2 : ℝ) : ℝ :=
  Real.cosh (2 * J1) * Real.cosh (2 * J2) * Real.cosh (2 * J3) +
    Real.sinh (2 * J1) * Real.sinh (2 * J2) * Real.sinh (2 * J3) -
    (Real.sinh (2 * J1) * Real.cos k1 +
      Real.sinh (2 * J2) * Real.cos k2 +
      Real.sinh (2 * J3) * Real.cos (k1 + k2))


noncomputable def triangularIsingHighTempSymbol
    (J1 J2 J3 k1 k2 : ℝ) : ℝ :=
  (1 + Real.tanh J1 ^ 2) * (1 + Real.tanh J2 ^ 2) *
      (1 + Real.tanh J3 ^ 2) +
    8 * Real.tanh J1 * Real.tanh J2 * Real.tanh J3 -
    2 * (Real.tanh J1 * (1 - Real.tanh J2 ^ 2) *
          (1 - Real.tanh J3 ^ 2) * Real.cos k1 +
      Real.tanh J2 * (1 - Real.tanh J1 ^ 2) *
          (1 - Real.tanh J3 ^ 2) * Real.cos k2 +
      Real.tanh J3 * (1 - Real.tanh J1 ^ 2) *
          (1 - Real.tanh J2 ^ 2) * Real.cos (k1 + k2))

end StatMech.FrontierA
