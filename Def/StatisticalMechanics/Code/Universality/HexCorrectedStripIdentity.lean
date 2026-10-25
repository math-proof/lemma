/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripIdentity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripStartReturn
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripLimits.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripIdentity


namespace StatMech.Universality

open Complex HexWalk

noncomputable section

def HexCSBoundaryExitLaw (T L : ℕ) (hT : 0 < T) : Prop :=
  ∀ (e : HexCSIncidence T L) (ts : List ℤ),
    e ∈ hexCSBoundaryIncidences T L →
    e ≠ hexCSStartIncidence T L hT →
    (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
        (ofTurns hexAWStart 1 ts).StaysIn
          (hexCSFiniteRegion T L hT).inRegion ∧
        (ofTurns hexAWStart 1 ts).EndsAt
          (hexAWMid e.vtx.1 e.edge) →
      hexInfra_midAccum hexAWStart 1 ts +
          halfStep (hexInfra_headAccum 1 ts) =
        hexAWMid e.vtx.1 e.edge +
          halfStep (hexCSCanonicalHeading e)


def HexCSBoundaryWindowLaw (T L : ℕ) (hT : 0 < T) : Prop :=
  ∀ (e : HexCSIncidence T L) (ts : List ℤ),
    e ∈ hexCSBoundaryIncidences T L →
    e ≠ hexCSStartIncidence T L hT →
    (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
        (ofTurns hexAWStart 1 ts).StaysIn
          (hexCSFiniteRegion T L hT).inRegion ∧
        (ofTurns hexAWStart 1 ts).EndsAt
          (hexAWMid e.vtx.1 e.edge) →
      ∃ w : ℤ,
        w ≤ hexInfra_headAccum 1 ts ∧
          hexInfra_headAccum 1 ts < w + 6 ∧
          w ≤ hexCSCanonicalHeading e ∧
          hexCSCanonicalHeading e < w + 6


end
end StatMech.Universality
