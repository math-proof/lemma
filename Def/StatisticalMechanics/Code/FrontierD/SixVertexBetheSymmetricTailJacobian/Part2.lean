/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricTailJacobian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricDensityJacobian
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheTailDensity
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricTailJacobian


namespace StatMech.FrontierD

noncomputable section

def sixVertexSymmetricJacobianDiagonalErrorOfLower
    (c : Real) (N : Nat) (lower : Real) : Real :=
  4 * Real.pi * N * (sixVertexFiniteRootDensityLipschitzConstant c : Real) *
      (1 / ((N : Real) * lower)) ^ 2 +
    2 * (sixVertexAnisotropyMagnitude c /
      (sixVertexAnisotropyMagnitude c - 1)) *
      (1 / ((N : Real) * lower))

end
end StatMech.FrontierD
