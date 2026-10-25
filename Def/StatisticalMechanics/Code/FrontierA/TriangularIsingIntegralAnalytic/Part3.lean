/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingIntegralAnalytic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingWeakAntiferromagnetic
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingIntegralAnalytic.Part2
open Filter MeasureTheory Topology Complex


namespace StatMech.FrontierA

noncomputable section

def triangularIsingComplexControl
    (beta J : Real) (z : Complex) : Real :=
  ‖Complex.cosh (2 * z) ^ 2 * Complex.cosh (2 * z * J) -
      (Real.cosh (2 * beta) ^ 2 * Real.cosh (2 * (beta * J)) : Real)‖ +
  ‖Complex.sinh (2 * z) ^ 2 * Complex.sinh (2 * z * J) -
      (Real.sinh (2 * beta) ^ 2 * Real.sinh (2 * (beta * J)) : Real)‖ +
  2 * ‖Complex.sinh (2 * z) - (Real.sinh (2 * beta) : Complex)‖ +
  ‖Complex.sinh (2 * z * J) -
      (Real.sinh (2 * (beta * J)) : Complex)‖ +
  ‖Complex.cosh (2 * z) - (Real.cosh (2 * beta) : Complex)‖ +
  ‖Complex.sinh (2 * z) - (Real.sinh (2 * beta) : Complex)‖ +
  ‖Complex.cosh (2 * z * J) -
      (Real.cosh (2 * (beta * J)) : Complex)‖ +
  ‖Complex.sinh (2 * z * J) -
      (Real.sinh (2 * (beta * J)) : Complex)‖

def triangularIsingComplexRadius (beta J : Real) : Real :=
  min (triangularIsingRayGap beta J / 2) 1

def triangularIsingComplexNeighborhood (beta J : Real) : Set Complex :=
  {z | triangularIsingComplexControl beta J z <
    triangularIsingComplexRadius beta J}

end
end StatMech.FrontierA
