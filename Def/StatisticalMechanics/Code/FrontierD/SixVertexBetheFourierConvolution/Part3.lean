/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierConvolution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierOrthogonality
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierConvolution.Part2


namespace StatMech.FrontierD

noncomputable section

def sixVertexFourierRootDensityNormBound (lam : Real) : Real :=
  1 / 2 + ∑' n : Nat, sixVertexFourierRootDensityMajorant lam n

end
end StatMech.FrontierD
