/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnAnnulusCharge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnCutInjection.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnAnnulusCharge.Part9


namespace StatMech.FrontierD

noncomputable section

noncomputable def FKRectZeroTurnAnnulusCharge.ofCrossing
    (R : FKRectTorus) (omega : R.Configuration)
    (crossing : FKRectZeroTurnCutRemainderComponent R omega →
      FKRectRawPrimalHorizontalCrossingComponent R omega)
    (hunique : ∀ C D,
      crossing C = crossing D →
      fkRectZeroTurnRemainderSide R omega C =
        fkRectZeroTurnRemainderSide R omega D → C = D) :
    FKRectZeroTurnAnnulusCharge R omega where
  crossing := crossing
  side := fkRectZeroTurnRemainderSide R omega
  injective_pair := by
    intro C D h
    injection h with hcross hside
    exact hunique C D hcross hside


noncomputable def FKRectZeroTurnAnnulusCharge.ofClusterMatching
    (R : FKRectTorus) (omega : R.Configuration)
    (hexists : ∀ C : FKRectZeroTurnCutRemainderComponent R omega,
      ∃ X : FKRectRawPrimalHorizontalCrossingComponent R omega,
        FKRectZeroTurnCrossingMatches R omega C X)
    (hunique : ∀ C D : FKRectZeroTurnCutRemainderComponent R omega,
      fkRectZeroTurnRemainderPrimalComponent R omega C =
          fkRectZeroTurnRemainderPrimalComponent R omega D →
        fkRectZeroTurnRemainderSide R omega C =
          fkRectZeroTurnRemainderSide R omega D → C = D) :
    FKRectZeroTurnAnnulusCharge R omega := by
  let crossing : FKRectZeroTurnCutRemainderComponent R omega →
      FKRectRawPrimalHorizontalCrossingComponent R omega := fun C =>
    Classical.choose (hexists C)
  apply FKRectZeroTurnAnnulusCharge.ofCrossing R omega crossing
  intro C D hcross hside
  apply hunique C D
  · have hC := Classical.choose_spec (hexists C)
    have hD := Classical.choose_spec (hexists D)
    exact hC.symm.trans ((congrArg
      (fkRectRawPrimalCrossingTorusComponent R omega) hcross).trans hD)
  · exact hside


noncomputable def FKRectZeroTurnAnnulusCharge.ofAnchor
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
    FKRectZeroTurnAnnulusCharge R omega :=
  FKRectZeroTurnAnnulusCharge.ofCrossing R omega crossing (by
    intro C D hcross hside
    apply Subtype.ext
    rw [← hanchor C, ← hanchor D, hcross, hside])


noncomputable def FKRectZeroTurnAnnulusCharge.ofExtremeDart
    (R : FKRectTorus) (omega : R.Configuration)
    (crossing : FKRectZeroTurnCutRemainderComponent R omega →
      FKRectRawPrimalHorizontalCrossingComponent R omega)
    (hextreme : ∀ C,
      (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
          (fkRectRawPrimalCrossingExtremeDart R omega (crossing C)
            (fkRectZeroTurnRemainderSide R omega C)) = C.1) :
    FKRectZeroTurnAnnulusCharge R omega :=
  FKRectZeroTurnAnnulusCharge.ofAnchor R omega crossing
    (fkRectRawPrimalCrossingExtremeDart R omega) hextreme

end
end StatMech.FrontierD
