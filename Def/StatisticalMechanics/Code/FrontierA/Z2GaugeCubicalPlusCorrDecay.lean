/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalPlusCorrDecay.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugePlusCorrDecay
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalTwoPointLimit
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFKCylinderGeometry.Part8
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFKInternalCylinder.Part5


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness StatMech.Lattice
  StatMech.Percolation

noncomputable section

def oddCubicalCenteredSite (m : Nat)
    (q : CubicalCell (oddCubeSide m) (oddCubeSide m) (oddCubeSide m)) :
    Site 3 :=
  (rectangularPrismSiteEquivSctBoxDobrushin m
    (oddCubicalCellEquivPrismSite m q)).1

end
end StatMech.FrontierA
