/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripGeometry.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripAssembly.Part2


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

def HexCSCanonicalWindingLaw (T L : ℕ) (hT : 0 < T) : Prop :=
  ∀ (e : HexCSIncidence T L) (ts : List ℤ),
    e ∈ hexCSBoundaryIncidences T L →
    e ≠ hexCSStartIncidence T L hT →
    (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
        (ofTurns hexAWStart 1 ts).StaysIn
          (hexCSFiniteRegion T L hT).inRegion ∧
        (ofTurns hexAWStart 1 ts).EndsAt
          (hexAWMid e.vtx.1 e.edge) →
      hexInfra_headAccum 1 ts = hexCSCanonicalHeading e

end
end StatMech.Universality
