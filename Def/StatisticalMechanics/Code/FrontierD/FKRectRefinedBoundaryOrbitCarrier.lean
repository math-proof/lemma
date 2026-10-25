/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundaryOrbitCarrier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedWalkCarrier.Part3


namespace StatMech.FrontierD

open Equiv

noncomputable section

def fkRectCanonicalRefinedBoundaryOrbitDarts
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus) :
    List FKRectIntegralSquareDart :=
  fkRectRefinedBoundaryDarts
    (fkRectConfigurationToMedialPairing R omega) d
    (fkRectRefinedBoundaryCanonicalCenter R d)
    (orderOf (fkMedialBoundaryStep
      (fkRectConfigurationToMedialPairing R omega)))


def fkRectCanonicalRefinedBoundaryOrbitCoverDarts
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus) :=
  fkRectSquareCoverDartList (fkRectRefinedCoverTorus R)
    (fkRectCanonicalRefinedBoundaryOrbitDarts R omega d)
    (fkRectRefinedBoundaryOrbitTranslation
      (fkRectConfigurationToMedialPairing R omega) d
      (fkRectRefinedBoundaryCanonicalCenter R d))


end
end StatMech.FrontierD
