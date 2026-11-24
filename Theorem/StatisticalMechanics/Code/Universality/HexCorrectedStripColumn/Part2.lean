module
public import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedColumnLength
public import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripFamilyMass.Part2
public import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripIdentity.Part2
public import Def.StatisticalMechanics.Code.Universality.HexCorrectedStripColumn.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripColumn.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open HexWalk

open scoped BigOperators

noncomputable section

@[simp] theorem hexCSTopColumn_colSum
    (T : ℕ) (hT : 0 < T)
    (hlocal : ∀ L, HexCSLocalRelation T L hT)
    (hwindow : ∀ L, HexCSBoundaryWindowLaw T L hT)
    (x : ℝ) :
    (hexCSTopColumn T hT hlocal hwindow).colSum x =
      ∑' w : {ts : List ℤ // HexCSTopWalkAtWidth T hT ts},
        x ^ (ofTurns hexAWStart 1 w.1).endpointNumVertices := rfl

end
end StatMech.Universality
