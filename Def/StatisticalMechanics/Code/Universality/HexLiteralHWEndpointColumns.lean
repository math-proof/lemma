/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWEndpointColumns.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWAugment.Part14
import Theorem.StatisticalMechanics.Code.Universality.HexHWBridgeSubsetBound.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWEndpointColumns


namespace StatMech.Universality

open HexWalk

open scoped BigOperators

noncomputable section

noncomputable def hlhe_activeCriticalMass
    (S : Finset HexHWContentHalf) (T : ℕ) : ℝ :=
  ∑ b ∈ hhs_activeBridges S with b.width = T,
    hhc_bridgeWeight hexChiE b


def hlhe_positiveGeom (r : ℝ) (T : ℕ) : ℝ :=
  if T = 0 then 0 else r ^ T

end
end StatMech.Universality
