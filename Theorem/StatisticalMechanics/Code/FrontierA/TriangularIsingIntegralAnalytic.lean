/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingIntegralAnalytic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingWeakAntiferromagnetic
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingIntegralAnalytic
open Filter MeasureTheory Topology Complex


namespace StatMech.FrontierA

noncomputable section

theorem triangularIsingRaySymbolComplex_ofReal
    (beta J p q : Real) :
    triangularIsingRaySymbolComplex J beta p q =
      (triangularIsingSymbol beta beta (beta * J) p q : Complex) := by
  have h2 : (2 : Complex) * beta = ((2 * beta : Real) : Complex) := by
    norm_num
  have hJ : ((2 * beta : Real) : Complex) * J =
      ((2 * (beta * J) : Real) : Complex) := by
    norm_num
    ring
  unfold triangularIsingRaySymbolComplex triangularIsingSymbol
  rw [h2, hJ, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh,
    ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
  push_cast
  ring


end
end StatMech.FrontierA
