/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonParity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonEmbedding.Part5


namespace StatMech.FrontierD

open StatMech.Onsager

open StatMech.Onsager.BaseCase

noncomputable section

def fkRectBlackOrbitMedialRibbonIndexEquiv
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    Fin (fkRectBlackOrbitMedialRibbonWord R omega d).length ≃
      Fin (fkRectBlackOrbitList
        (fkRectConfigurationToMedialPairing R omega) d).length × Fin 8 :=
  (finCongr (by
    rw [fkRectBlackOrbitMedialRibbonWord_length]
    omega)).trans finProdFinEquiv.symm


def fkRectBlackOrbitMedialRibbonFlatSite
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus)
    (k : Fin (fkRectBlackOrbitMedialRibbonWord R omega d).length) :
    ZMod (8 * R.medialTorus.width) ×
      ZMod (8 * R.medialTorus.height) :=
  fkRectBlackOrbitMedialRibbonIndexedSite R omega d
    (fkRectBlackOrbitMedialRibbonIndexEquiv R omega d k)

end
end StatMech.FrontierD
