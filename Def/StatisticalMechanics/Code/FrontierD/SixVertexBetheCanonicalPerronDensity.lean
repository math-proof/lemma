/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronDensity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEventualPerronBranch.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricStabilityEstimate.Part4
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexPerronGaugeThreshold
    {c : Real} (hc : 2 < c) (n : Nat) : Nat := by
  classical
  exact if hn : n = 0 then 0 else
    Classical.choose (eventually_atTop.1
      (eventually_exists_sixVertexHalfFilledPerronGaugeWitness
        (epsilon := (1 : Real) / (n : Real) ^ 8) hc
        (by
          apply one_div_pos.mpr
          positivity)))

end
end StatMech.FrontierD
