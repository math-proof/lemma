/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheTailLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheTailSelectedDensity
import Mathlib.Topology.ContinuousMap.Ordered
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheTailLimit.Part2


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
