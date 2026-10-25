/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthBoundaryWinding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripOrbits.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointVertex.Part14
import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthBoundaryWinding.Part3


namespace StatMech.Universality

open Complex HexWalk

open scoped BigOperators

noncomputable section

def hexAWLowerSlantWitness (L : ℕ) : HexAWIncidence 2 L :=
  ⟨⟨hexAWLowerSlantWitnessCoord L,
      hexAWLowerSlantWitnessCoord_mem L⟩, 1⟩


def hexAWUpperSlantWitness (L : ℕ) : HexAWIncidence 2 L :=
  ⟨⟨hexAWUpperSlantWitnessCoord L,
      hexAWUpperSlantWitnessCoord_mem L⟩, 2⟩

end
end StatMech.Universality
