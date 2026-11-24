module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheTailSelectedDensity
public import Mathlib.Topology.ContinuousMap.Ordered
public import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheTailLimit.Part2


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

theorem tendsto_sixVertexSelectedWeightedDensityMap
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c) :
    Tendsto (sixVertexSelectedWeightedDensityMap hc) atTop
      (nhds (sixVertexTailWeightedDensityLimitMap hc htail)) :=
  Classical.choose_spec (cauchySeq_tendsto_of_complete
    (cauchySeq_sixVertexSelectedWeightedDensityMap hc htail))

end
end StatMech.FrontierD
