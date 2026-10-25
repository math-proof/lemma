/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingIntegralAnalytic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingWeakAntiferromagnetic
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingIntegralAnalytic.Part3
open Filter MeasureTheory Topology Complex


namespace StatMech.FrontierA

noncomputable section

def triangularIsingLogRaySymbolComplexDeriv
    (J : Real) (z : Complex) (p q : Real) : Complex :=
  triangularIsingRaySymbolComplexDeriv J z p q /
    triangularIsingRaySymbolComplex J z p q

def triangularIsingComplexDerivBound (beta J : Real) : Real :=
  let C := |Real.cosh (2 * beta)| + 1
  let S := |Real.sinh (2 * beta)| + 1
  let CJ := |Real.cosh (2 * (beta * J))| + 1
  let SJ := |Real.sinh (2 * (beta * J))| + 1
  4 * C * S * CJ + 2 * |J| * C ^ 2 * SJ +
    4 * S * C * SJ + 2 * |J| * S ^ 2 * CJ +
    4 * C + 2 * |J| * CJ

end
end StatMech.FrontierA
