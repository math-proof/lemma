module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierOrthogonality
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierConvolution.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierConvolution.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def sixVertexFourierRootDensityNormBound (lam : Real) : Real :=
  1 / 2 + ∑' n : Nat, sixVertexFourierRootDensityMajorant lam n

end
end StatMech.FrontierD
