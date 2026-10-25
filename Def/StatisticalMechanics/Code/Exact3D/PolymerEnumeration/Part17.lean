/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Theorem.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part14


namespace StatMech

namespace Exact3D

open StatMech.Lattice

noncomputable section

namespace BoundedPolymerCase

noncomputable def ofLocalCoordinateAnchoredAt {d R maxDegree maxRange : ℕ}
    (c : LocalPolymerCoordinate d) {a : Site d}
    (ha : a ∈ c.support)
    (hdiam : c.support.coordinateDiameterBound R)
    (hdegree : c.degree ≤ maxDegree) (hrange : c.range ≤ maxRange) :
    BoundedPolymerCase d R maxDegree maxRange :=
  ofLocalCoordinate (translateLocalCoordinate c (-a))
    (by
      simpa [translateLocalCoordinate] using
        PolymerSupport.containedInBox_translate_neg_of_mem_of_coordinateDiameterBound
          ha hdiam)
    (by simpa [translateLocalCoordinate] using hdegree)
    (by simpa [translateLocalCoordinate] using hrange)

end BoundedPolymerCase
end
end Exact3D
end StatMech
