/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealSimple.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveIdealTurns


namespace StatMech.FrontierA

theorem KWSmallAdaptiveConnectorScales.idealRawSimpleData
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (neighborhood : KWVertexNeighborhoodData polygon)
    (scales : KWSmallAdaptiveConnectorScales polygon neighborhood.scale)
    (hM : 2 ≤ M)
    (hcross : ∀ i : Fin n, kwComplexCross (polygon.edgeVector i)
      (polygon.edgeVector (i + 1)) ≠ 0)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0) :
    let patch := scales.toPatchedData hM
    KWRawNonbacktrackingSimpleData patch.idealVertex := by
  dsimp only
  let patch := scales.toPatchedData hM
  apply KWRawNonbacktrackingSimpleData.of_turnAdmissible
  · calc
      3 ≤ n := polygon.three_le
      _ = n * 1 := by omega
      _ ≤ n * (2 * (M + 1)) :=
        Nat.mul_le_mul_left n (by omega)
  · exact patch.idealRawEdge_ne_zero
  · exact patch.idealTurnAdmissible hcoords
  · exact scales.ideal_nonincident_disjoint neighborhood hM hcross hcoords

end StatMech.FrontierA
