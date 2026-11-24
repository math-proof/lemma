module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheContinuousOffsetFourier.Part4
public import Mathlib.Topology.MetricSpace.Antilipschitz
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetProfileRegularity.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetProfileRegularity.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def sixVertexRapidityMomentumDerivativeFloor (lam : Real) : Real :=
  Real.sinh lam / (Real.cosh lam + 1)

end
end StatMech.FrontierD
