module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheTailSelectedDensity
public import Mathlib.Topology.ContinuousMap.Ordered
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheTailLimit.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheTailLimit.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

open Filter Topology

def sixVertexTailWeightedDensityLimit
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c) : Real → Real :=
  sixVertexTailWeightedDensityLimitMap hc htail |>.IccExtend
    (by linarith [Real.pi_pos])

def sixVertexTailRootDensity
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c) (x : Real) : Real :=
  sixVertexTailWeightedDensityLimit hc htail x /
    sixVertexRootDensityWeight c x

end
end StatMech.FrontierD
