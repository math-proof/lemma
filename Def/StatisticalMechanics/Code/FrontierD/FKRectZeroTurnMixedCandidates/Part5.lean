/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnMixedCandidates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.FKRectMedialDualShift.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedAnnulusCharge
import Structure.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedCandidates
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

noncomputable def FKRectZeroTurnMixedTouchedCertificate.ofBranchUniqueness
    (R : FKRectTorus) (omega : R.Configuration)
    (hprimal : ∀ C D : FKRectZeroTurnCutRemainderComponent R omega,
      fkRectZeroTurnRemainderPrimalComponent R omega C =
          fkRectZeroTurnRemainderPrimalComponent R omega D →
        fkRectZeroTurnRemainderSide R omega C =
          fkRectZeroTurnRemainderSide R omega D → C = D)
    (hdual : ∀ C D : FKRectZeroTurnCutRemainderComponent R omega,
      ∀ X : FKRectRawWiredDualHorizontalCrossingComponent R omega,
        X ∈ fkRectZeroTurnDualTouchedCrossings R omega C →
        X ∈ fkRectZeroTurnDualTouchedCrossings R omega D →
        fkRectZeroTurnRemainderSide R omega C =
          fkRectZeroTurnRemainderSide R omega D → C = D) :
    FKRectZeroTurnMixedTouchedCertificate R omega where
  nonempty := fkRectZeroTurnMixedTouchedCrossings_nonempty R omega
  sameSide_unique := by
    intro C D X hXC hXD hside
    cases X with
    | inl X =>
        have hC :=
          (mem_fkRectZeroTurnMixedTouchedCrossings_inl_iff R omega C X).1 hXC
        have hD :=
          (mem_fkRectZeroTurnMixedTouchedCrossings_inl_iff R omega D X).1 hXD
        exact hprimal C D
          (fkRectZeroTurnRemainderPrimalComponent_eq_of_shared_touchedCrossing
            R omega C D X hC.2 hD.2) hside
    | inr X =>
        have hC :=
          (mem_fkRectZeroTurnMixedTouchedCrossings_inr_iff R omega C X).1 hXC
        have hD :=
          (mem_fkRectZeroTurnMixedTouchedCrossings_inr_iff R omega D X).1 hXD
        exact hdual C D X hC.2 hD.2 hside


noncomputable def fkRectZeroTurnSelectedMixedCrossing
    (R : FKRectTorus) (omega : R.Configuration)
    (certificate : FKRectZeroTurnMixedTouchedCertificate R omega)
    (C : FKRectZeroTurnCutRemainderComponent R omega) :
    FKRectRawPrimalWiredDualHorizontalCrossingComponent R omega :=
  (certificate.nonempty C).choose

end
end StatMech.FrontierD
