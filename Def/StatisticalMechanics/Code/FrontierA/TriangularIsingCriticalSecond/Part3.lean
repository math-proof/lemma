/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalSecond.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalC1.Part6
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalSecond.Part2
open Filter MeasureTheory Topology
open scoped Real Interval


namespace StatMech.FrontierA

noncomputable section

def triangularIsingRayLogDeriv2Clamp
    (beta J c epsilon p q : Real) : Real :=
  let den := max (triangularIsingSymbol beta beta (beta * J) p q)
    (c * epsilon ^ 2)
  let d2 := triangularIsingRaySymbolDeriv2 J beta 0 0 +
    4 * Real.sinh (2 * beta) *
      ((1 - Real.cos p) + (1 - Real.cos q)) +
    4 * J ^ 2 * Real.sinh (2 * beta * J) *
      (1 - Real.cos (p + q))
  d2 / den - (triangularIsingRaySymbolDeriv J beta p q / den) ^ 2

end
end StatMech.FrontierA
