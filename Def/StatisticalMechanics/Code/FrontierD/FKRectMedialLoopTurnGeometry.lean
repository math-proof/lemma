/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialLoopTurnGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedEdgeCenterClass
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTurnWalk.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialLoopTurnGeometry


namespace StatMech.FrontierD

noncomputable section

def fkRectBlackDartSite (R : FKRectTorus)
    (d : FKMedialBlackDart R.medialTorus) :=
  let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
  fkRectIntegralSquarePointMod L
    (fkRectRefinedDartPoint
      (fkRectRefinedBoundaryCanonicalCenter R d.1) d.1.2)


def fkRectBlackDartShiftedPoint (R : FKRectTorus)
    (u : Int × Int) (d : FKMedialBlackDart R.medialTorus) :=
  let A := fkRectSquareDeckTranslation R u
  let c := fkRectRefinedBoundaryCanonicalCenter R d.1
  fkRectRefinedDartPoint
    (c.1 + 4 * A.1, c.2 + 4 * A.2) d.1.2


def fkRectBlackDartShiftedSite (R : FKRectTorus)
    (u : Int × Int) (d : FKMedialBlackDart R.medialTorus) :=
  fkRectIntegralSquarePointMod
    (fkRectSquareCoverSide (fkRectRefinedCoverTorus R))
    (fkRectBlackDartShiftedPoint R u d)

end
end StatMech.FrontierD
