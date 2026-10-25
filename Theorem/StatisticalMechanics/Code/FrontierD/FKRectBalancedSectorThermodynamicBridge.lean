/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedSectorThermodynamicBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBalancedSectorNormalization.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectNoLoopNormalization
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4CorrelationReduction
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedShareGluing.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddWallisLimit.Part2
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem le_negLog_div_of_le_exp_neg_mul
    {mass height rate : Real} (hmass : 0 < mass) (hheight : 0 < height)
    (hupper : mass <= Real.exp (-rate * height)) :
    rate <= -Real.log mass / height := by
  have hlog : Real.log mass <= -rate * height := by
    calc
      Real.log mass <= Real.log (Real.exp (-rate * height)) :=
        Real.log_le_log hmass hupper
      _ = -rate * height := Real.log_exp _
  rw [le_div_iff₀ hheight]
  linarith


end
end StatMech.FrontierD
