/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeStability.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricStabilityEstimate.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheInfiniteAnisotropyGauge
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeStability


namespace StatMech.FrontierD

noncomputable section

def sixVertexRootDensityKernelUniformBound (c : Real) : Real :=
  (sixVertexAnisotropyMagnitude c /
      (sixVertexAnisotropyMagnitude c - 1)) *
    ((sixVertexAnisotropyMagnitude c + 1) /
      sixVertexRootDensityScale c)

end
end StatMech.FrontierD
