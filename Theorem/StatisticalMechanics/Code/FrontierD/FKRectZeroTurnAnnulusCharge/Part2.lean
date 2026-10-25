/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnAnnulusCharge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnCutInjection.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnAnnulusCharge.Part2


namespace StatMech.FrontierD

noncomputable section

theorem fkRectRawPrimalCrossingFirstRow_component
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectRawPrimalHorizontalCrossingComponent R omega) :
    (fkRectOpenGraph R
      (fkRectForceCutClosed R omega)).connectedComponentMk
        (fkRectLeftColumn R,
          fkRectRawPrimalCrossingFirstRow R omega C) = C.1 := by
  apply (mem_fkRectRawPrimalCrossingLeftRows R omega C _).1
  exact Finset.min'_mem _ _

theorem fkRectRawPrimalCrossingLastRow_component
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectRawPrimalHorizontalCrossingComponent R omega) :
    (fkRectOpenGraph R
      (fkRectForceCutClosed R omega)).connectedComponentMk
        (fkRectLeftColumn R,
          fkRectRawPrimalCrossingLastRow R omega C) = C.1 := by
  apply (mem_fkRectRawPrimalCrossingLeftRows R omega C _).1
  exact Finset.max'_mem _ _

theorem fkRectRawPrimalCrossingFirstRow_injective
    (R : FKRectTorus) (omega : R.Configuration) :
    Function.Injective
      (fkRectRawPrimalCrossingFirstRow R omega) := by
  intro C D hrow
  apply Subtype.ext
  calc
    C.1 = (fkRectOpenGraph R
          (fkRectForceCutClosed R omega)).connectedComponentMk
            (fkRectLeftColumn R,
              fkRectRawPrimalCrossingFirstRow R omega C) :=
      (fkRectRawPrimalCrossingFirstRow_component R omega C).symm
    _ = (fkRectOpenGraph R
          (fkRectForceCutClosed R omega)).connectedComponentMk
            (fkRectLeftColumn R,
              fkRectRawPrimalCrossingFirstRow R omega D) := by rw [hrow]
    _ = D.1 := fkRectRawPrimalCrossingFirstRow_component R omega D

theorem fkRectRawPrimalCrossingLastRow_injective
    (R : FKRectTorus) (omega : R.Configuration) :
    Function.Injective
      (fkRectRawPrimalCrossingLastRow R omega) := by
  intro C D hrow
  apply Subtype.ext
  calc
    C.1 = (fkRectOpenGraph R
          (fkRectForceCutClosed R omega)).connectedComponentMk
            (fkRectLeftColumn R,
              fkRectRawPrimalCrossingLastRow R omega C) :=
      (fkRectRawPrimalCrossingLastRow_component R omega C).symm
    _ = (fkRectOpenGraph R
          (fkRectForceCutClosed R omega)).connectedComponentMk
            (fkRectLeftColumn R,
              fkRectRawPrimalCrossingLastRow R omega D) := by rw [hrow]
    _ = D.1 := fkRectRawPrimalCrossingLastRow_component R omega D


end
end StatMech.FrontierD
