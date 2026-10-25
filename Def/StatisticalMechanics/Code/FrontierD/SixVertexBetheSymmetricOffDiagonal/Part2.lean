/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricOffDiagonal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricScatteringBound.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricCovering
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricOffDiagonal
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexSymmetricTailJacobianOffDiagonalError
    (c : Real) (N : Nat) : Real :=
  ((2 * Real.pi) *
      (sixVertexSymmetricScatteringLipschitzConstant c : Real) +
    2 * (sixVertexAnisotropyMagnitude c /
      (sixVertexAnisotropyMagnitude c - 1))) *
    (1 / ((N : Real) * sixVertexTailFiniteDensityFloor c))


end
end StatMech.FrontierD
