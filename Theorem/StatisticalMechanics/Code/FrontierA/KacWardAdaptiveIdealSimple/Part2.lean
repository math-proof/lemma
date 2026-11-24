module
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveIdealTurns
public import Def.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveIdealSimple


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealSimple.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

@[simp] theorem KWSmallAdaptiveConnectorScales.idealSimplePolygon_vertex
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (neighborhood : KWVertexNeighborhoodData polygon)
    (scales : KWSmallAdaptiveConnectorScales polygon neighborhood.scale)
    (hM : 2 ≤ M)
    (hcross : ∀ i : Fin n, kwComplexCross (polygon.edgeVector i)
      (polygon.edgeVector (i + 1)) ≠ 0)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0) :
    (scales.idealSimplePolygon neighborhood hM hcross hcoords).vertex =
      (scales.toPatchedData hM).idealVertex := rfl

end StatMech.FrontierA
