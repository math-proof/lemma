/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripLimits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripAssembly.Part14
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripLimits


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

def HexCSSideWalk (T L : ℕ) (hT : 0 < T) (ts : List ℤ) : Prop :=
  (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
    (ofTurns hexAWStart 1 ts).StaysIn
      (hexCSFiniteRegion T L hT).inRegion ∧
    ∃ c : HexAWCoord,
      c ∈ hexCSVertexSet T L ∧ c.color = .black ∧
        hexAWDepth c = 0 ∧
        hexAWMid c 0 ≠ hexAWStart ∧
        (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c 0)


def HexCSTopWalk (T L : ℕ) (hT : 0 < T) (ts : List ℤ) : Prop :=
  (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
    (ofTurns hexAWStart 1 ts).StaysIn
      (hexCSFiniteRegion T L hT).inRegion ∧
    ∃ c : HexAWCoord,
      c ∈ hexCSVertexSet T L ∧ c.color = .white ∧
        hexAWDepth c = T ∧
        (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c 0)


def HexCSSlantWalk (T L : ℕ) (hT : 0 < T) (ts : List ℤ) : Prop :=
  (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
    (ofTurns hexAWStart 1 ts).StaysIn
      (hexCSFiniteRegion T L hT).inRegion ∧
    ∃ c : HexAWCoord,
      c ∈ hexCSVertexSet T L ∧ c.color = .white ∧
        ((c.i = L ∧
            (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c 1)) ∨
          (c.j = L ∧
            (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c 2)))

end
end StatMech.Universality
