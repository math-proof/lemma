module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricTailJacobian.Part3
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheKernelQuadrature
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricScatteringBound.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricScatteringBound.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def sixVertexSymmetricScatteringBoundaryBound (c : Real) : Real :=
  4 * Real.arctan
    (1 / (2 * sixVertexAnisotropyMagnitude c *
      Real.sqrt (sixVertexAnisotropyMagnitude c ^ 2 - 1)))

end
end StatMech.FrontierD
