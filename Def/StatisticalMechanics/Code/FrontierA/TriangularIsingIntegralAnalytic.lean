/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingIntegralAnalytic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingWeakAntiferromagnetic
open Filter MeasureTheory Topology Complex


namespace StatMech.FrontierA

noncomputable section

def triangularIsingRaySymbolComplex
    (J : Real) (z : Complex) (p q : Real) : Complex :=
  Complex.cosh (2 * z) ^ 2 * Complex.cosh (2 * z * J) +
    Complex.sinh (2 * z) ^ 2 * Complex.sinh (2 * z * J) -
    (Complex.sinh (2 * z) * ((Real.cos p : Complex) + Real.cos q) +
      Complex.sinh (2 * z * J) * (Real.cos (p + q) : Complex))


def triangularIsingRaySymbolComplexDeriv
    (J : Real) (z : Complex) (p q : Real) : Complex :=
  4 * Complex.cosh (2 * z) * Complex.sinh (2 * z) *
      Complex.cosh (2 * z * J) +
    2 * J * Complex.cosh (2 * z) ^ 2 * Complex.sinh (2 * z * J) +
    4 * Complex.sinh (2 * z) * Complex.cosh (2 * z) *
      Complex.sinh (2 * z * J) +
    2 * J * Complex.sinh (2 * z) ^ 2 * Complex.cosh (2 * z * J) -
    2 * Complex.cosh (2 * z) * ((Real.cos p : Complex) + Real.cos q) -
    2 * J * Complex.cosh (2 * z * J) * (Real.cos (p + q) : Complex)

end
end StatMech.FrontierA
