/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronDensity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEventualPerronBranch.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricStabilityEstimate.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronDensity
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexPerronGaugeStage
    {c : Real} (hc : 2 < c) (k : Nat) : Nat := by
  classical
  exact Nat.findGreatest
    (fun n => sixVertexPerronGaugeThreshold hc n ≤ k)
      (Nat.sqrt (Nat.sqrt (Nat.sqrt (k + 1))))

end
end StatMech.FrontierD
