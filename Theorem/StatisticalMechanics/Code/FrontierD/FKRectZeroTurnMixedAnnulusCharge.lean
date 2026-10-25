/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnMixedAnnulusCharge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnAnnulusCharge.Part10
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualBoundaryWiring
import Def.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedAnnulusCharge


namespace StatMech.FrontierD

noncomputable section

theorem card_fkRectRawWiredDualHorizontalCrossingComponent
    (R : FKRectTorus) (omega : R.Configuration) :
    Fintype.card
        (FKRectRawWiredDualHorizontalCrossingComponent R omega) =
      fkRectRawHorizontalCrossingClusterCount R
        (fkRectDualConfigurationEquiv R
          (fkRectForceCutClosed R omega)) := by
  unfold fkRectRawHorizontalCrossingClusterCount
  exact Fintype.card_congr (Equiv.refl _)

theorem card_fkRectZeroTurnCutRemainderComponent_mixed
    (R : FKRectTorus) (omega : R.Configuration) :
    Fintype.card (FKRectZeroTurnCutRemainderComponent R omega) =
      fkRectZeroTurnCutRemainderCount R omega := by
  classical
  unfold FKRectZeroTurnCutRemainderComponent
    fkRectZeroTurnCutRemainderCount
  exact Fintype.card_ofFinset
    (fkRectZeroTurnCutRemainderComponents R omega) (by simp)

theorem card_fkRectRawPrimalHorizontalCrossingComponent_mixed
    (R : FKRectTorus) (omega : R.Configuration) :
    Fintype.card (FKRectRawPrimalHorizontalCrossingComponent R omega) =
      fkRectRawHorizontalCrossingClusterCount R
        (fkRectForceCutClosed R omega) := by
  unfold fkRectRawHorizontalCrossingClusterCount
  exact Fintype.card_congr (Equiv.refl _)

theorem card_fkRectRawPrimalWiredDualHorizontalCrossingComponent
    (R : FKRectTorus) (omega : R.Configuration) :
    Fintype.card
        (FKRectRawPrimalWiredDualHorizontalCrossingComponent R omega) =
      fkRectRawPrimalDualHorizontalCrossingClusterCount R
        (fkRectForceCutClosed R omega) := by
  rw [Fintype.card_sum,
    card_fkRectRawPrimalHorizontalCrossingComponent_mixed,
    card_fkRectRawWiredDualHorizontalCrossingComponent]
  rfl


theorem fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimalDual_of_mixedCharge
    (R : FKRectTorus) (omega : R.Configuration)
    (charge : FKRectZeroTurnMixedAnnulusCharge R omega) :
    fkRectZeroTurnCutRemainderCount R omega ≤
      2 * fkRectRawPrimalDualHorizontalCrossingClusterCount R
        (fkRectForceCutClosed R omega) := by
  let encode : FKRectZeroTurnCutRemainderComponent R omega →
      FKRectRawPrimalWiredDualHorizontalCrossingComponent R omega × Bool :=
    fun C => (charge.crossing C, charge.side C)
  have hcard := Fintype.card_le_of_injective encode charge.injective_pair
  rw [card_fkRectZeroTurnCutRemainderComponent_mixed] at hcard
  rw [Fintype.card_prod, Fintype.card_bool,
    card_fkRectRawPrimalWiredDualHorizontalCrossingComponent] at hcard
  omega


theorem fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_add_two_of_mixedCharge
    (R : FKRectTorus) (omega : R.Configuration)
    (charge : FKRectZeroTurnMixedAnnulusCharge R omega) :
    fkRectZeroTurnCutRemainderCount R omega ≤
      2 * fkRectRawHorizontalCrossingClusterCount R
          (fkRectForceCutClosed R omega) + 2 := by
  have hcharge :=
    fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimalDual_of_mixedCharge
      R omega charge
  have hdual := fkRectRawHorizontalCrossingClusterCount_dual_le_one
    R (fkRectForceCutClosed R omega)
      (fkRectCutClosedConfiguration_forceCutClosed R omega)
  unfold fkRectRawPrimalDualHorizontalCrossingClusterCount at hcharge
  omega


theorem fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_add_two_of_mixedCrossing
    (R : FKRectTorus) (omega : R.Configuration)
    (crossing : FKRectZeroTurnCutRemainderComponent R omega →
      FKRectRawPrimalWiredDualHorizontalCrossingComponent R omega)
    (hunique : ∀ C D,
      crossing C = crossing D →
      fkRectZeroTurnRemainderSide R omega C =
        fkRectZeroTurnRemainderSide R omega D → C = D) :
    fkRectZeroTurnCutRemainderCount R omega ≤
      2 * fkRectRawHorizontalCrossingClusterCount R
          (fkRectForceCutClosed R omega) + 2 :=
  fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_add_two_of_mixedCharge
    R omega
      (FKRectZeroTurnMixedAnnulusCharge.ofCrossing
        R omega crossing hunique)


theorem fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_add_two_of_mixedAnchor
    (R : FKRectTorus) (omega : R.Configuration)
    (crossing : FKRectZeroTurnCutRemainderComponent R omega →
      FKRectRawPrimalWiredDualHorizontalCrossingComponent R omega)
    (anchor :
      FKRectRawPrimalWiredDualHorizontalCrossingComponent R omega →
        Bool → FKMedialDart R.medialTorus)
    (hanchor : ∀ C,
      (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
          (anchor (crossing C)
            (fkRectZeroTurnRemainderSide R omega C)) = C.1) :
    fkRectZeroTurnCutRemainderCount R omega ≤
      2 * fkRectRawHorizontalCrossingClusterCount R
          (fkRectForceCutClosed R omega) + 2 :=
  fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_add_two_of_mixedCharge
    R omega
      (FKRectZeroTurnMixedAnnulusCharge.ofAnchor
        R omega crossing anchor hanchor)

end
end StatMech.FrontierD
