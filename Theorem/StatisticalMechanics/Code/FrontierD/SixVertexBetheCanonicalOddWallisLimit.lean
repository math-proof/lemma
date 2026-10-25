/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallisLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddWallisBridge.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddWallisFixed.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddAveragedDensityEndpoints
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddWallisLimit


namespace StatMech.FrontierD

open Filter Topology Finset

noncomputable section

theorem tendsto_sixVertexCanonicalOddFixedHalfIncrementSum
    {c : Real} (hc : 2 < c) (s : Nat) :
    Tendsto (sixVertexCanonicalOddFixedHalfIncrementSum hc s) atTop
      (nhds (Real.log (Real.cosh (sixVertexAntiferroelectricLambda c)) +
        Real.log Real.pi - Real.log (c ^ 2))) := by
  exact tendsto_sixVertexCanonicalOddFixedHalfIncrement hc s

end
end StatMech.FrontierD
