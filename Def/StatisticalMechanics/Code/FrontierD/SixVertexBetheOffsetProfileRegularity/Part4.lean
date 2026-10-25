/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetProfileRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheContinuousOffsetFourier.Part4
import Mathlib.Topology.MetricSpace.Antilipschitz
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetProfileRegularity.Part3


namespace StatMech.FrontierD

noncomputable section

def sixVertexMomentumRapidityLipschitzNNReal
    (lam : Real) : NNReal :=
  Real.toNNReal (1 / sixVertexRapidityMomentumDerivativeFloor lam)

end
end StatMech.FrontierD
