/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalC1.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingIntegralAnalytic.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalParameter.Part2
open Filter MeasureTheory Topology
open scoped Real Interval


namespace StatMech.FrontierA

noncomputable section

def triangularIsingRaySymbolDeriv
    (J beta p q : Real) : Real :=
  4 * Real.cosh (2 * beta) * Real.sinh (2 * beta) *
      Real.cosh (2 * beta * J) +
    2 * J * Real.cosh (2 * beta) ^ 2 * Real.sinh (2 * beta * J) +
    4 * Real.sinh (2 * beta) * Real.cosh (2 * beta) *
      Real.sinh (2 * beta * J) +
    2 * J * Real.sinh (2 * beta) ^ 2 * Real.cosh (2 * beta * J) -
    2 * Real.cosh (2 * beta) * (Real.cos p + Real.cos q) -
    2 * J * Real.cosh (2 * beta * J) * Real.cos (p + q)

end
end StatMech.FrontierA
