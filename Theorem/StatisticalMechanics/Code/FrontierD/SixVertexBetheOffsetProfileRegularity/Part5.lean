/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetProfileRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheContinuousOffsetFourier.Part4
import Mathlib.Topology.MetricSpace.Antilipschitz
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetProfileRegularity.Part5


namespace StatMech.FrontierD

noncomputable section

theorem lipschitzWith_sixVertexContinuousOffsetFourier
    {c : Real} (hc : 2 < c) :
    LipschitzWith (sixVertexContinuousOffsetFourierLipschitzNNReal c)
      (sixVertexContinuousOffsetFourier c hc) := by
  simpa [sixVertexContinuousOffsetFourierLipschitzNNReal,
      sixVertexContinuousOffsetFourier, Function.comp_def, mul_comm] using
    (lipschitzWith_sixVertexOffsetRapidityProfile
        (sixVertexAntiferroelectricLambda_pos hc)).comp
      (lipschitzWith_sixVertexMomentumRapidity
        (sixVertexAntiferroelectricLambda_pos hc))

end
end StatMech.FrontierD
