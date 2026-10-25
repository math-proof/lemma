/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronDensity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEventualPerronBranch.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricStabilityEstimate.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronDensity.Part2
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexCanonicalDensityPerronBetheRoots
    {c : Real} (hc : 2 < c) (k : Nat) :
    Fin ((k + 1) + (k + 1)) → Real := by
  classical
  let stage := sixVertexPerronGaugeStage hc k
  exact if hs : 0 < stage then
      Classical.choose
        (sixVertexPerronGaugeThreshold_spec hc hs k
          (sixVertexPerronGaugeStage_threshold_le hc k))
    else
      sixVertexCanonicalPerronBetheRoots hc k

end
end StatMech.FrontierD
