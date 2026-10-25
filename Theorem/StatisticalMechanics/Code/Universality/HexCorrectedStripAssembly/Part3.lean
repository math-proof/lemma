/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripGeometry.Part11
import Def.StatisticalMechanics.Code.Universality.HexCorrectedStripAssembly.Part3


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

theorem hexCS_deterministic_winding_of_law {T L : ℕ} {hT : 0 < T}
    (hlaw : HexCSCanonicalWindingLaw T L hT)
    (e : HexCSIncidence T L) (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (ts : List ℤ)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge)) :
    (ofTurns hexAWStart 1 ts).turning = hexCSCanonicalWinding e := by
  unfold hexCSCanonicalWinding
  simpa only [Int.cast_one] using
    (hexInfra_turning_const_of_finalHeading hexAWStart 1 ts
      (hexCSCanonicalHeading e) (hlaw e ts he hne hadm))


end
end StatMech.Universality
