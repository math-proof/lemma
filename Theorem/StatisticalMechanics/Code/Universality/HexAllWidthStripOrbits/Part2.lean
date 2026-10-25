/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripOrbits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part18
import Theorem.StatisticalMechanics.Code.Universality.HexMirrorOrbitBoundary.Part3
import Def.StatisticalMechanics.Code.Universality.HexAllWidthStripOrbits.Part2


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

@[simp] theorem hexAWDomainInteriorPairing_interior
    (T L : ℕ) (hT : 0 < T)
    (hlocal : HexAWLocalRelation T L hT) :
    (hexAWDomainInteriorPairing T L hT hlocal).interior =
      hexAWInteriorIncidences T L := rfl

theorem hexAWDomainInteriorPairing_interior_sub
    (T L : ℕ) (hT : 0 < T)
    (hlocal : HexAWLocalRelation T L hT) :
    (hexAWDomainInteriorPairing T L hT hlocal).interior ⊆
      (hexAWDomain T L hT hlocal).incidences := by
  apply hexAWInteriorPairingOfDomain_interior_sub
  intro v
  simp


end
end StatMech.Universality
