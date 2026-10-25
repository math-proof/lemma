/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRegularizedLogTaylor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalCandidateBoundaryLimit


namespace StatMech.FrontierD

noncomputable section

def sixVertexRegularizedBetheLogNormSecondDerivative
    (c epsilon x : Real) : Real :=
  let a := c ^ 2 - 1
  let A := a ^ 2 + 1 + 2 * a * Real.cos x
  let B := 2 - 2 * Real.cos x + epsilon
  (-a * Real.cos x * A - 2 * a ^ 2 * Real.sin x ^ 2) / A ^ 2 +
    (-Real.cos x * B + 2 * Real.sin x ^ 2) / B ^ 2

def sixVertexRegularizedBetheLogNormSecondDerivativeBound
    (c epsilon : Real) : Real :=
  (c ^ 2 - 1) / (c ^ 2 - 2) ^ 2 +
    2 * (c ^ 2 - 1) ^ 2 / (c ^ 2 - 2) ^ 4 +
    1 / epsilon + 2 / epsilon ^ 2

end
end StatMech.FrontierD
