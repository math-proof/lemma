/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalSecond.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalC1.Part6
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalSecond
open Filter MeasureTheory Topology
open scoped Real Interval


namespace StatMech.FrontierA

noncomputable section

theorem hasDerivAt_triangularIsingRaySymbolDeriv
    (J beta p q : Real) :
    HasDerivAt (fun b => triangularIsingRaySymbolDeriv J b p q)
      (triangularIsingRaySymbolDeriv2 J beta p q) beta := by
  exact (differentiable_triangularIsingRaySymbolDeriv J p q beta).hasDerivAt


end
end StatMech.FrontierA
