/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheTailLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheTailSelectedDensity
import Mathlib.Topology.ContinuousMap.Ordered
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheTailLimit


namespace StatMech.FrontierD

noncomputable section

open Filter Topology

def sixVertexTailWeightedDensityLimitMap
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c) :
    C(Set.Icc (-Real.pi) Real.pi, Real) :=
  Classical.choose (cauchySeq_tendsto_of_complete
    (cauchySeq_sixVertexSelectedWeightedDensityMap hc htail))

end
end StatMech.FrontierD
