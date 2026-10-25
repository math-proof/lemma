/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalPolynomial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingSymbol.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalPolynomial.Part4


namespace StatMech.FrontierA

noncomputable def triangularIsingCriticalRateAlongDeriv (β J : ℝ) : ℝ :=
  4 * Real.sinh (2 * β) * Real.cosh (2 * β) +
    4 * Real.cosh (2 * β) * Real.sinh (2 * (β * J)) +
    4 * J * Real.sinh (2 * β) * Real.cosh (2 * (β * J))

end StatMech.FrontierA
