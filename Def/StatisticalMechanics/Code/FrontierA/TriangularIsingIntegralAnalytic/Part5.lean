/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingIntegralAnalytic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingWeakAntiferromagnetic
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingIntegralAnalytic.Part4
open Filter MeasureTheory Topology Complex


namespace StatMech.FrontierA

noncomputable section

def triangularIsingFreeEnergyRayComplex (J : Real) (z : Complex) : Complex :=
  -(Real.log 2 : Complex) - (1 / (8 * Real.pi ^ 2) : Complex) *
    ∫ p in (-Real.pi)..Real.pi,
      ∫ q in (-Real.pi)..Real.pi,
        Complex.log (triangularIsingRaySymbolComplex J z p q)

end
end StatMech.FrontierA
