/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingPhaseKernel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalMomentum
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingSymbolBounds
import Theorem.StatisticalMechanics.Code.Onsager.PhaseRegularity.Part12
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingPhaseKernel.Part2
open Filter MeasureTheory Topology


namespace StatMech.FrontierA

noncomputable section

def triangularIsingCriticalInverseSymbolClamp
    (beta J c epsilon p q : Real) : Real :=
  1 / max (triangularIsingSymbol beta beta (beta * J) p q)
    (c * epsilon ^ 2)

end
end StatMech.FrontierA
