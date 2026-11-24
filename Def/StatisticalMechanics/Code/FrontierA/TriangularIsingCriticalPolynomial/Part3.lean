module
public import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingSymbol.Part2
public import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalPolynomial.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalPolynomial.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

noncomputable def triangularIsingCriticalRate (x y : ℝ) : ℝ :=
  Real.sinh (2 * x) ^ 2 +
    2 * Real.sinh (2 * x) * Real.sinh (2 * y)

end StatMech.FrontierA
