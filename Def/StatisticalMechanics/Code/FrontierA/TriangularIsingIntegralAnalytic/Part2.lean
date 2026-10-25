/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingIntegralAnalytic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingWeakAntiferromagnetic
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingIntegralAnalytic
open Filter MeasureTheory Topology Complex


namespace StatMech.FrontierA

noncomputable section

def triangularIsingRayGap (beta J : Real) : Real :=
  if 0 <= J then
    triangularIsingSymbol beta beta (beta * J) 0 0
  else if 0 <= Real.sinh (2 * beta) +
      2 * Real.sinh (2 * (beta * J)) then
    triangularIsingSymbol beta beta (beta * J) 0 0
  else
    Real.cosh (2 * beta) ^ 2 * Real.cosh (2 * (beta * J)) +
      Real.sinh (2 * beta) ^ 2 * Real.sinh (2 * (beta * J)) +
      Real.sinh (2 * beta) ^ 2 /
        (2 * Real.sinh (2 * (beta * J))) +
      Real.sinh (2 * (beta * J))

end
end StatMech.FrontierA
