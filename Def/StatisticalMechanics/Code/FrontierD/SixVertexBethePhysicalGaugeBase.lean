module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSechFourier.Part3
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheGaugeAsymptotics.Part2
open Filter Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalGaugeBase.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def sixVertexFourierPhysicalDensityMap
    {c : Real} (hc : 2 < c) : C(Real, Real) :=
  ⟨sixVertexFourierPhysicalDensity c hc,
    continuous_sixVertexFourierPhysicalDensity hc⟩

end
end StatMech.FrontierD
