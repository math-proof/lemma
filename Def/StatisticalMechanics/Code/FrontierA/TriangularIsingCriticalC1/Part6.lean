/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalC1.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingIntegralAnalytic.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalParameter.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalC1.Part5
open Filter MeasureTheory Topology
open scoped Real Interval


namespace StatMech.FrontierA

noncomputable section

def triangularIsingCriticalLogBound (m J b y : Real) : Real :=
  |Real.log m| + |Real.log (triangularIsingRaySymbolAbsBound J b)| +
    |Real.log (1 - Real.cos y)|

end
end StatMech.FrontierA
