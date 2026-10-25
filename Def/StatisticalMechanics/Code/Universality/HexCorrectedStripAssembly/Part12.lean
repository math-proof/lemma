/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripGeometry.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripAssembly.Part10


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

noncomputable def hexCSBoundaryFixed
    (T L : ℕ) (hT : 0 < T) (hlocal : HexCSLocalRelation T L hT)
    (hlaw : HexCSCanonicalWindingLaw T L hT)
    (k : HexCSFixedIndex T L hT) :
    HexFixedBoundaryPoint (hexCSDomain T L hT hlocal)
      (@hexCSHeading T L) :=
  endpointFixedBoundaryPoint_of_winding
    (@hexCSHeading T L) (fun _ => rfl) k.1
    (hexCSCanonicalHeading k.1) rfl
    (hexCSCanonicalWinding k.1)
    (fun ts hadm => hexCS_deterministic_winding_of_law hlaw k.1 k.2.1
      k.2.2.2 ts hadm)
    (by
      rw [hexCSFixedIndex_heading_one k, hexCSFixedIndex_winding_zero k]
      simp [hexPhase_sideTilt])

end
end StatMech.Universality
