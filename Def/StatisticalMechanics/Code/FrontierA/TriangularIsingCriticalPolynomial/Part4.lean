/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalPolynomial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingSymbol.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalPolynomial.Part3


namespace StatMech.FrontierA

noncomputable def triangularIsingCriticalFactor (x y : ℝ) : ℝ :=
  -triangularIsingCriticalCompanion (Real.tanh x) (Real.tanh y) /
    ((1 - Real.tanh x ^ 2) ^ 2 * (1 - Real.tanh y ^ 2))

end StatMech.FrontierA
