/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalPolynomial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingSymbol.Part2


namespace StatMech.FrontierA

def triangularIsingCriticalPolynomial (t r : ℝ) : ℝ :=
  1 + t ^ 2 * r - 2 * t - r - t ^ 2 - 2 * t * r


end StatMech.FrontierA
