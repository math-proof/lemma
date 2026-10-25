/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelHallCapacity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelHallCapacity
open Finset SimpleGraph Set


namespace StatMech.Universality

noncomputable section

theorem rlc_twoChannelPIMSFixedPayloadCapacity_iff_nonempty_packing
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma') :
    RlcTwoChannelPIMSFixedPayloadCapacity hclosure ↔
      Nonempty (RlcTwoChannelPIMSDiscardedPayloadPacking hclosure) := by
  constructor
  · intro hcapacity
    exact ⟨rlc_twoChannelPIMSDiscardedPayloadPackingOfCapacity
      hclosure hcapacity⟩
  · rintro ⟨packing⟩ eta
    letI := Fintype.ofFinite (RlcTwoChannelTargetFibre
      (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure) eta)
    letI := Fintype.ofFinite (ConfigSpace
      (RlcTwoChannelPIMSFixedPayloadSlot
        (rlc_twoChannelCanonicalRoute eta)))
    simpa only [Nat.card_eq_fintype_card] using
      Fintype.card_le_of_embedding
        (rlc_twoChannelPIMSFixedPayloadEmbeddingOfPacking packing eta)

end
end StatMech.Universality
