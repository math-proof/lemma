/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalC1.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingIntegralAnalytic.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalParameter.Part2
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalC1.Part2
open Filter MeasureTheory Topology
open scoped Real Interval


namespace StatMech.FrontierA

noncomputable section

theorem hasDerivAt_log_triangularIsingSymbol_along_ray
    {J b p q : Real}
    (hpos : 0 < triangularIsingSymbol b b (b * J) p q) :
    HasDerivAt
      (fun t => Real.log (triangularIsingSymbol t t (t * J) p q))
      (triangularIsingRayLogDeriv J b p q) b := by
  simpa only [triangularIsingRayLogDeriv] using
    (hasDerivAt_triangularIsingSymbol_along_ray J b p q).log hpos.ne'


end
end StatMech.FrontierA
