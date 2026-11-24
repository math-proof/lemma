module
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPolygonTurning.Part2
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardFourSignMajority
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardHalfPlaneSegment
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardInteriorSideSplice
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAntipodalExclusion
public import Mathlib.Data.List.Rotate
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardFinitePolygonEar.Part7


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

noncomputable def KWFiniteSimplePolygon.removeVertexOne
    {m : ℕ} (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3))
    (hsimple : polygon.VertexOneRemovalIsSimple) :
    KWFiniteSimplePolygon (m + 2) where
  vertex := kwRemoveVertexOne polygon.vertex
  three_le := by omega
  vertex_injective := polygon.vertex_injective.comp
    (Fin.succAbove_right_injective (p := (1 : Fin (m + 3))))
  vertex_not_strictly_between := hsimple.1
  edgeInteriors_disjoint := hsimple.2

end StatMech.FrontierA
