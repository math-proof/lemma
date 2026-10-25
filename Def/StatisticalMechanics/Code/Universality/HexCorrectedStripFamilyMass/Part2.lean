/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripFamilyMass.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripMasses
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripFamilyMass


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

def HexCSClassWalk
    (T L : ℕ) (hT : 0 < T) (cls : HexPairedBoundaryClass)
    (ts : List ℤ) : Prop :=
  (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
    (ofTurns hexAWStart 1 ts).StaysIn
      (hexCSFiniteRegion T L hT).inRegion ∧
    ∃ e ∈ hexCSClassIncidences T L hT cls,
      (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid e.vtx.1 e.edge)

end
end StatMech.Universality
