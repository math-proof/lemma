/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalC1.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingIntegralAnalytic.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalParameter.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalC1
open Filter MeasureTheory Topology
open scoped Real Interval


namespace StatMech.FrontierA

noncomputable section

def triangularIsingRayLogDeriv (J b p q : Real) : Real :=
  triangularIsingRaySymbolDeriv J b p q /
    triangularIsingSymbol b b (b * J) p q

end
end StatMech.FrontierA
