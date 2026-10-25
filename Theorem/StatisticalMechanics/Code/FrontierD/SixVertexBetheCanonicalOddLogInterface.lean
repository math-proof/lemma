/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddLogInterface.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalCandidateDecomposition
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddLogInterface


namespace StatMech.FrontierD

open Filter Topology

noncomputable section

theorem eventually_sixVertexCanonicalFixedChargeCandidate_odd_eq_density
    {c : Real} (hc : 2 < c) (s : Nat) :
    (fun k => sixVertexCanonicalFixedChargeBetheCandidateLogRatio hc
      (2 * s + 1) k) =ᶠ[atTop]
      sixVertexCanonicalFixedOddDensityCandidateLogRatio hc s := by
  filter_upwards
    [eventually_sixVertexCanonicalFixedOddDensityBetheEigenvalueValue_eq hc s]
      with k hk
  unfold sixVertexCanonicalFixedChargeBetheCandidateLogRatio
    sixVertexFixedChargeBetheEigenvalueValue
    sixVertexCanonicalFixedOddDensityCandidateLogRatio
  rw [dif_neg (Nat.not_even_iff_odd.2 ⟨s, rfl⟩)]
  have hindex : (2 * s + 1 - 1) / 2 = s := by omega
  rw [hindex, <- hk]

theorem eventually_sixVertexCanonicalFixedOddDensityCandidate_decomposition
    {c : Real} (hc : 2 < c) (s : Nat) :
    ∀ᶠ k : Nat in atTop,
      sixVertexCanonicalFixedOddDensityCandidateLogRatio hc s k =
        sixVertexCanonicalOddZeroModeWallisCorrection hc s k +
          2 * sixVertexCanonicalOddBulkLogDisplacement hc s k -
          2 * sixVertexCanonicalOddBoundaryLogSum hc s k := by
  filter_upwards
    [eventually_sixVertexCanonicalFixedOddDensityPerronBetheRoots_witness hc s]
      with k hk
  rw [sixVertexCanonicalFixedOddDensityCandidateLogRatio_decomposition
    hc s k hk]
  simp only [sixVertexCanonicalOddZeroModeWallisCorrection,
    sixVertexCanonicalOddBulkLogDisplacement,
    sixVertexCanonicalOddBoundaryLogSum]
  ring


end
end StatMech.FrontierD
