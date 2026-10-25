/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnAnnulusCharge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnCutInjection.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnAnnulusCharge.Part10


namespace StatMech.FrontierD

noncomputable section

theorem card_fkRectZeroTurnCutRemainderComponent
    (R : FKRectTorus) (omega : R.Configuration) :
    Fintype.card (FKRectZeroTurnCutRemainderComponent R omega) =
      fkRectZeroTurnCutRemainderCount R omega := by
  classical
  unfold FKRectZeroTurnCutRemainderComponent
    fkRectZeroTurnCutRemainderCount
  exact Fintype.card_ofFinset
    (fkRectZeroTurnCutRemainderComponents R omega) (by simp)

theorem card_fkRectRawPrimalHorizontalCrossingComponent
    (R : FKRectTorus) (omega : R.Configuration) :
    Fintype.card (FKRectRawPrimalHorizontalCrossingComponent R omega) =
      fkRectRawHorizontalCrossingClusterCount R
        (fkRectForceCutClosed R omega) := by
  unfold fkRectRawHorizontalCrossingClusterCount
  exact Fintype.card_congr (Equiv.refl _)


theorem fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_of_annulusCharge
    (R : FKRectTorus) (omega : R.Configuration)
    (charge : FKRectZeroTurnAnnulusCharge R omega) :
    fkRectZeroTurnCutRemainderCount R omega ≤
      2 * fkRectRawHorizontalCrossingClusterCount R
        (fkRectForceCutClosed R omega) := by
  let encode : FKRectZeroTurnCutRemainderComponent R omega →
      FKRectRawPrimalHorizontalCrossingComponent R omega × Bool :=
    fun C => (charge.crossing C, charge.side C)
  have hcard := Fintype.card_le_of_injective encode charge.injective_pair
  rw [card_fkRectZeroTurnCutRemainderComponent] at hcard
  rw [Fintype.card_prod, Fintype.card_bool,
    card_fkRectRawPrimalHorizontalCrossingComponent] at hcard
  omega


theorem fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_of_crossing
    (R : FKRectTorus) (omega : R.Configuration)
    (crossing : FKRectZeroTurnCutRemainderComponent R omega →
      FKRectRawPrimalHorizontalCrossingComponent R omega)
    (hunique : ∀ C D,
      crossing C = crossing D →
      fkRectZeroTurnRemainderSide R omega C =
        fkRectZeroTurnRemainderSide R omega D → C = D) :
    fkRectZeroTurnCutRemainderCount R omega ≤
      2 * fkRectRawHorizontalCrossingClusterCount R
        (fkRectForceCutClosed R omega) :=
  fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_of_annulusCharge
    R omega (FKRectZeroTurnAnnulusCharge.ofCrossing R omega crossing hunique)


theorem fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_of_clusterMatching
    (R : FKRectTorus) (omega : R.Configuration)
    (hexists : ∀ C : FKRectZeroTurnCutRemainderComponent R omega,
      ∃ X : FKRectRawPrimalHorizontalCrossingComponent R omega,
        FKRectZeroTurnCrossingMatches R omega C X)
    (hunique : ∀ C D : FKRectZeroTurnCutRemainderComponent R omega,
      fkRectZeroTurnRemainderPrimalComponent R omega C =
          fkRectZeroTurnRemainderPrimalComponent R omega D →
        fkRectZeroTurnRemainderSide R omega C =
          fkRectZeroTurnRemainderSide R omega D → C = D) :
    fkRectZeroTurnCutRemainderCount R omega ≤
      2 * fkRectRawHorizontalCrossingClusterCount R
        (fkRectForceCutClosed R omega) :=
  fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_of_annulusCharge
    R omega (FKRectZeroTurnAnnulusCharge.ofClusterMatching
      R omega hexists hunique)


theorem fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_of_anchor
    (R : FKRectTorus) (omega : R.Configuration)
    (crossing : FKRectZeroTurnCutRemainderComponent R omega →
      FKRectRawPrimalHorizontalCrossingComponent R omega)
    (anchor : FKRectRawPrimalHorizontalCrossingComponent R omega →
      Bool → FKMedialDart R.medialTorus)
    (hanchor : ∀ C,
      (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
          (anchor (crossing C)
            (fkRectZeroTurnRemainderSide R omega C)) = C.1) :
    fkRectZeroTurnCutRemainderCount R omega ≤
      2 * fkRectRawHorizontalCrossingClusterCount R
        (fkRectForceCutClosed R omega) :=
  fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_of_annulusCharge
    R omega (FKRectZeroTurnAnnulusCharge.ofAnchor
      R omega crossing anchor hanchor)


theorem fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_of_extremeDart
    (R : FKRectTorus) (omega : R.Configuration)
    (crossing : FKRectZeroTurnCutRemainderComponent R omega →
      FKRectRawPrimalHorizontalCrossingComponent R omega)
    (hextreme : ∀ C,
      (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
          (fkRectRawPrimalCrossingExtremeDart R omega (crossing C)
            (fkRectZeroTurnRemainderSide R omega C)) = C.1) :
    fkRectZeroTurnCutRemainderCount R omega ≤
      2 * fkRectRawHorizontalCrossingClusterCount R
        (fkRectForceCutClosed R omega) :=
  fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_of_annulusCharge
    R omega (FKRectZeroTurnAnnulusCharge.ofExtremeDart
      R omega crossing hextreme)

end
end StatMech.FrontierD
