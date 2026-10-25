/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetOperatorQuadrature.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargePeriodicQuadrature
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetTaylor
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheContinuousOffset.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetOperatorQuadrature


namespace StatMech.FrontierD

noncomputable section

def sixVertexOffsetQuotientLipschitzBound
    (c lower G D : Real) : Real :=
  (sixVertexThetaLeftKernelLipschitzBound c * G +
      (sixVertexAnisotropyMagnitude c /
        (sixVertexAnisotropyMagnitude c - 1)) * D) / lower +
    (sixVertexAnisotropyMagnitude c /
      (sixVertexAnisotropyMagnitude c - 1)) * G *
        (sixVertexFiniteRootDensityLipschitzConstant c : Real) / lower ^ 2

def sixVertexOffsetQuotientLipschitzNNReal
    (c lower G D : Real) : NNReal :=
  Real.toNNReal (sixVertexOffsetQuotientLipschitzBound c lower G D)

end
end StatMech.FrontierD
