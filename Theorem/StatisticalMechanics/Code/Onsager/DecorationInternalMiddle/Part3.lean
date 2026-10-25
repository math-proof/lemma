/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationInternalMiddle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationInternalEndpoint
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Def.StatisticalMechanics.Code.Onsager.DecorationInternalMiddle.Part3


namespace StatMech.Onsager

open Matrix BigOperators


theorem ons_decMiddleAugmented_det
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ)
    (omega u v t : ℂ) (homega : omega ≠ 0)
    (site : ZMod L × ZMod L) :
    (1 - ons_decMiddleAugmented L decWeight omega u v t site).det =
      (1 - ons_KWmatDecorationWeightedPhase L
        (ons_scaleDecEdgeWeight decWeight
          (ons_decChainEdge site 1) t) omega u v).det := by
  let M₀ := ons_KWmatDecorationWeightedPhase L
    (ons_scaleDecEdgeWeight decWeight
      (ons_decChainEdge site 1) 0) omega u v
  let U := ons_decMiddleU L decWeight omega site
  let V := ons_decMiddleV L decWeight omega u v site
  have hblock :
      1 - ons_decMiddleAugmented L decWeight omega u v t site =
        Matrix.fromBlocks (1 - M₀) (-U) (-(t • V)) 1 := by
    ext i j
    cases i <;> cases j <;>
      simp [ons_decMiddleAugmented, M₀, U, V, Matrix.one_apply]
  have hmul : (-U) * (-(t • V)) = t • (U * V) := by
    ext i j
    simp [Matrix.mul_apply]
    ring
  rw [hblock, Matrix.det_fromBlocks_one₂₂, hmul]
  have hrank :=
    ons_KWmatDecorationWeightedPhase_scaleMiddle_rankTwo
      L decWeight omega u v t homega site
  have hrank' :
      ons_KWmatDecorationWeightedPhase L
          (ons_scaleDecEdgeWeight decWeight
            (ons_decChainEdge site 1) t) omega u v =
        M₀ + t • (U * V) := by
    simpa only [M₀, U, V] using hrank
  rw [show 1 - M₀ - t • (U * V) =
      1 - (M₀ + t • (U * V)) by abel]
  rw [← hrank']

end StatMech.Onsager
