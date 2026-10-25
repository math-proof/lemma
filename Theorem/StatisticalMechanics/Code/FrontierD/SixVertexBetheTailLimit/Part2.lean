/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheTailLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheTailSelectedDensity
import Mathlib.Topology.ContinuousMap.Ordered
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheTailLimit.Part2


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
