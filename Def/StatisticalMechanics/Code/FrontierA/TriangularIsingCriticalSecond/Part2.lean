/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalSecond.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalC1.Part6
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalSecond
open Filter MeasureTheory Topology
open scoped Real Interval


namespace StatMech.FrontierA

noncomputable section

def triangularIsingRayLogDeriv2 (J beta p q : Real) : Real :=
  (triangularIsingRaySymbolDeriv2 J beta p q *
      triangularIsingSymbol beta beta (beta * J) p q -
    triangularIsingRaySymbolDeriv J beta p q ^ 2) /
      triangularIsingSymbol beta beta (beta * J) p q ^ 2

end
end StatMech.FrontierA
