/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricOffDiagonal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricScatteringBound.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricCovering
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricOffDiagonal.Part2
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexSymmetricTailJacobianTotalError (c : Real) (N : Nat) : Real :=
  sixVertexSymmetricTailJacobianDiagonalError c N +
    sixVertexSymmetricTailJacobianOffDiagonalError c N

def sixVertexSymmetricJacobianOffDiagonalErrorOfLower
    (c : Real) (N : Nat) (lower : Real) : Real :=
  ((2 * Real.pi) *
      (sixVertexSymmetricScatteringLipschitzConstant c : Real) +
    2 * (sixVertexAnisotropyMagnitude c /
      (sixVertexAnisotropyMagnitude c - 1))) *
    (1 / ((N : Real) * lower))

def sixVertexSymmetricJacobianTotalErrorOfLower
    (c : Real) (N : Nat) (lower : Real) : Real :=
  sixVertexSymmetricJacobianDiagonalErrorOfLower c N lower +
    sixVertexSymmetricJacobianOffDiagonalErrorOfLower c N lower

end
end StatMech.FrontierD
