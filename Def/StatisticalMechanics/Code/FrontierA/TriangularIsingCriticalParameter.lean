/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalParameter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalMomentum
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalParameter
open Filter Topology


namespace StatMech.FrontierA

noncomputable section

def triangularIsingCriticalPolynomialAlong (J β : ℝ) : ℝ :=
  triangularIsingCriticalPolynomial (Real.tanh β) (Real.tanh (β * J))

def triangularIsingCriticalFactorAlong (J β : ℝ) : ℝ :=
  triangularIsingCriticalFactor β (β * J)

def triangularIsingZeroModePrefactorAlong (J β : ℝ) : ℝ :=
  Real.cosh β ^ 4 * Real.cosh (β * J) ^ 2

end
end StatMech.FrontierA
