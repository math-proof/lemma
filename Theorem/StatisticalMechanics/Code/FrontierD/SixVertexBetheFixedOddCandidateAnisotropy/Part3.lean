/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedOddCandidateAnisotropy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedEvenCandidateAnisotropy.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhaseSingle.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedOddCandidateAnisotropy.Part2
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem tendsto_sixVertexFixedOddChargeNormalizedMProduct (s k : Nat) :
    Tendsto (sixVertexFixedOddChargeNormalizedMProduct s k) atTop
      (nhds (sixVertexFixedOddChargeLimitingMProduct s k)) := by
  unfold sixVertexFixedOddChargeNormalizedMProduct
    sixVertexFixedOddChargeLimitingMProduct
  apply tendsto_finsetProd
  intro j hj
  have hjne : j ≠ sixVertexFixedChargeBetheCentralIndex (2 * s + 1) k :=
    (Finset.mem_erase.mp hj).1
  exact continuous_norm.continuousAt.tendsto.comp
    (tendsto_sixVertexFixedChargeBetheM_normalized (2 * s + 1) k j
      (sixVertexFixedOddLimitingPhase_ne_one_of_ne_central s k j hjne))


end
end StatMech.FrontierD
