/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnMixedAnnulusCharge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnAnnulusCharge.Part10
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualBoundaryWiring
import Structure.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedAnnulusCharge


namespace StatMech.FrontierD

noncomputable section

noncomputable def FKRectZeroTurnMixedAnnulusCharge.ofCrossing
    (R : FKRectTorus) (omega : R.Configuration)
    (crossing : FKRectZeroTurnCutRemainderComponent R omega →
      FKRectRawPrimalWiredDualHorizontalCrossingComponent R omega)
    (hunique : ∀ C D,
      crossing C = crossing D →
      fkRectZeroTurnRemainderSide R omega C =
        fkRectZeroTurnRemainderSide R omega D → C = D) :
    FKRectZeroTurnMixedAnnulusCharge R omega where
  crossing := crossing
  side := fkRectZeroTurnRemainderSide R omega
  injective_pair := by
    intro C D h
    injection h with hcross hside
    exact hunique C D hcross hside


noncomputable def FKRectZeroTurnMixedAnnulusCharge.ofAnchor
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
    FKRectZeroTurnMixedAnnulusCharge R omega :=
  FKRectZeroTurnMixedAnnulusCharge.ofCrossing R omega crossing (by
    intro C D hcross hside
    apply Subtype.ext
    rw [← hanchor C, ← hanchor D, hcross, hside])

end
end StatMech.FrontierD
