/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFibreCube.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelVisibleFibreHall.Part2
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFibreCube.Part3
open Finset SimpleGraph Set


namespace StatMech.Universality

noncomputable section

theorem rlc_twoChannelPIMSPooledVisibleFibreCapacity_of_fullPIMSPhysicalSuccess
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
    (hphysical : RlcTwoChannelFullPIMSPhysicalSuccess gamma gamma') :
    RlcTwoChannelPIMSPooledVisibleFibreCapacity hclosure := by
  intro base
  apply Fintype.card_le_of_embedding
  exact
    { toFun := fun rho =>
        (rlc_twoChannelSuccessVisibleFibreEquivFixedPayload base).symm
          ⟨rlc_twoChannelFailureComplementFixedBits rho.1, by
            have hconfig : rlc_twoChannelConfigOfVisibleFixed base
                (rlc_twoChannelFailureComplementFixedBits rho.1) =
              rlc_twoChannelFullPIMSConfig gamma gamma' rho.1 := by
              calc
                _ = rlc_twoChannelConfigOfVisibleFixed
                    (rlc_twoChannelFailureVisibleBase hclosure rho.1)
                    (rlc_twoChannelFailureComplementFixedBits rho.1) := by
                      rw [rho.2]
                _ = _ :=
                  rlc_twoChannelConfigOfFailureComplement_eq_fullPIMS
                    hclosure rho.1
            rw [hconfig]
            exact hphysical rho.1⟩
      inj' := by
        intro rho sigma h
        have hpayload := congrArg
          (rlc_twoChannelSuccessVisibleFibreEquivFixedPayload base) h
        have hbits :
            rlc_twoChannelFailureComplementFixedBits rho.1 =
              rlc_twoChannelFailureComplementFixedBits sigma.1 := by
          simpa using congrArg Subtype.val hpayload
        exact (rlc_twoChannelFailureComplementFixedEmbedding base).injective
          hbits }


theorem rlc_twoChannelPIMSPooledVisibleFibreCapacity_iff_fixedPayload
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma') :
    RlcTwoChannelPIMSPooledVisibleFibreCapacity hclosure ↔
      forall base : RlcTwoChannelPIMSVisibleBase gamma gamma',
        Fintype.card (RlcTwoChannelFailureVisibleFibre hclosure base) <=
          Fintype.card (RlcTwoChannelSuccessFixedPayload base) := by
  constructor <;> intro h base
  · rw [← Fintype.card_congr
      (rlc_twoChannelSuccessVisibleFibreEquivFixedPayload base)]
    exact h base
  · rw [Fintype.card_congr
      (rlc_twoChannelSuccessVisibleFibreEquivFixedPayload base)]
    exact h base

end
end StatMech.Universality
