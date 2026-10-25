/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalLogUnregularizationBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalLogUnregularization.Part3


namespace StatMech.FrontierD

open Filter Topology

noncomputable section

theorem tendsto_sixVertexCanonicalEvenBulkLogDisplacement_bridge
    {c : Real} (hc : 2 < c) (s : Nat) :
    Tendsto (sixVertexCanonicalEvenBulkLogDisplacement hc s) atTop
      (nhds ((2 * s : Real) / 2 *
        (Real.log (Real.cosh (sixVertexAntiferroelectricLambda c)) -
          sixVertexAntiferroelectricGapRate
            (sixVertexAntiferroelectricLambda c)))) :=
  tendsto_sixVertexCanonicalEvenBulkLogDisplacement hc s

end
end StatMech.FrontierD
