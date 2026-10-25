/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripOrbits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part18
import Theorem.StatisticalMechanics.Code.Universality.HexMirrorOrbitBoundary.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripOrbits


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

def hexAWDomainInteriorPairing (T L : ℕ) (hT : 0 < T)
    (hlocal : HexAWLocalRelation T L hT) :
    (hexAWDomain T L hT hlocal).InteriorPairing :=
  hexAWInteriorPairingOfDomain (hexAWDomain T L hT hlocal)
    (fun _ => rfl) (fun _ _ => rfl)

end
end StatMech.Universality
