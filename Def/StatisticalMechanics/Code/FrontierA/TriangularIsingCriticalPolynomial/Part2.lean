/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalPolynomial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingSymbol.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalPolynomial


namespace StatMech.FrontierA

def triangularIsingCriticalCompanion (t r : ℝ) : ℝ :=
  1 + 2 * t - t ^ 2 + (1 - 2 * t - t ^ 2) * r

end StatMech.FrontierA
