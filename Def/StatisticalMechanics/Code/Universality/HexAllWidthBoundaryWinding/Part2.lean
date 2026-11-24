module
public import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripOrbits.Part6
public import Theorem.StatisticalMechanics.Code.Universality.HexEndpointVertex.Part14
public import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthBoundaryWinding.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthBoundaryWinding.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open Complex HexWalk

open scoped BigOperators

noncomputable section

def hexAWLowerSlantWitnessCoord (L : ℕ) : HexAWCoord :=
  ⟨-(L : ℤ) - 1, (L : ℤ), .black⟩


def hexAWUpperSlantWitnessCoord (L : ℕ) : HexAWCoord :=
  ⟨(L : ℤ), -(L : ℤ) - 1, .black⟩

end
end StatMech.Universality
