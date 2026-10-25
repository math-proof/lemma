/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalSecond.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalC1.Part6
open Filter MeasureTheory Topology
open scoped Real Interval


namespace StatMech.FrontierA

noncomputable section

def triangularIsingRaySymbolDeriv2 (J beta p q : Real) : Real :=
  deriv (fun b => triangularIsingRaySymbolDeriv J b p q) beta

end
end StatMech.FrontierA
