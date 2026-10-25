/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetTaylor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetLinearBound


namespace StatMech.FrontierD

noncomputable section

def sixVertexThetaDerivativeLipschitzNNReal (c : Real) : NNReal :=
  Real.toNNReal (sixVertexThetaLeftKernelLipschitzBound c)

def sixVertexThetaCrossLipschitzBound (c : Real) : Real :=
  sixVertexRootDensityKernelLipschitzBound c /
    ((sixVertexAnisotropyMagnitude c - 1) /
      sixVertexRootDensityScale c)

def sixVertexThetaTaylorBound (c : Real) : Real :=
  sixVertexThetaLeftKernelLipschitzBound c +
    sixVertexThetaCrossLipschitzBound c

end
end StatMech.FrontierD
