/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetBoundaryEstimate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetBoundarySource
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricStabilityEstimate.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheContinuousOffset.Part2


namespace StatMech.FrontierD

open Finset

noncomputable section

def sixVertexThetaRightLipschitzNNReal (c : Real) : NNReal :=
  Real.toNNReal (sixVertexAnisotropyMagnitude c /
    (sixVertexAnisotropyMagnitude c - 1))

end
end StatMech.FrontierD
