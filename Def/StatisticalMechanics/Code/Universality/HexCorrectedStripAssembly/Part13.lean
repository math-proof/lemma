/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripGeometry.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripAssembly.Part11


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

def HexCSStartReturnLaw (T L : ℕ) (hT : 0 < T) : Prop :=
  ∀ ts : List ℤ,
    (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
        (ofTurns hexAWStart 1 ts).StaysIn
          (hexCSFiniteRegion T L hT).inRegion ∧
        (ofTurns hexAWStart 1 ts).EndsAt hexAWStart →
      ts = []


end
end StatMech.Universality
