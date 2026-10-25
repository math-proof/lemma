/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitWindingGeometry.Part10
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonEmbedding.Part3


namespace StatMech.FrontierD

open StatMech.Onsager

open StatMech.Onsager.BaseCase

noncomputable section

def fkRectMedialRibbonBlockSite
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialBlackDart R.medialTorus) (t : Fin 8) :
    ZMod (8 * R.medialTorus.width) ×
      ZMod (8 * R.medialTorus.height) :=
  let o := fkRectMedialRibbonBlockOffset (pairing d.1.1) d.1.2 t
  (((8 * d.1.1.1.val : Nat) : Int) + o.1,
    ((8 * d.1.1.2.val : Nat) : Int) + o.2)


def fkRectMedialRibbonBlockCode
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialBlackDart R.medialTorus) (t : Fin 8) :
    (Fin R.medialTorus.width × Fin 8) ×
      (Fin R.medialTorus.height × Fin 8) :=
  let o := fkRectMedialRibbonBlockOffset (pairing d.1.1) d.1.2 t
  (fkRectRibbonNormalizeCell R.medialTorus.width_pos d.1.1.1 o.1,
    fkRectRibbonNormalizeCell R.medialTorus.height_pos d.1.1.2 o.2)

end
end StatMech.FrontierD
