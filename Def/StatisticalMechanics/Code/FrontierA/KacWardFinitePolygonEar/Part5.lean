/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPolygonTurning.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardFourSignMajority
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardHalfPlaneSegment
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardInteriorSideSplice
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAntipodalExclusion
import Mathlib.Data.List.Rotate
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardFinitePolygonEar.Part5


namespace StatMech.FrontierA

def KWFiniteSimplePolygon.VertexOneRemovalIsSimple
    {m : ℕ} (polygon : KWFiniteSimplePolygon (m + 3)) : Prop :=
  (∀ (i j : Fin (m + 2)), j ≠ i → j ≠ i + 1 →
      ¬Sbtw ℝ (kwRemoveVertexOne polygon.vertex i)
        (kwRemoveVertexOne polygon.vertex j)
        (kwRemoveVertexOne polygon.vertex (i + 1))) ∧
    ∀ (i j : Fin (m + 2)), i ≠ j →
      Disjoint
        {z : ℂ | Sbtw ℝ (kwRemoveVertexOne polygon.vertex i) z
          (kwRemoveVertexOne polygon.vertex (i + 1))}
        {z : ℂ | Sbtw ℝ (kwRemoveVertexOne polygon.vertex j) z
          (kwRemoveVertexOne polygon.vertex (j + 1))}


def KWFiniteSimplePolygon.VertexOneDiagonalIsClean
    {m : ℕ} (polygon : KWFiniteSimplePolygon (m + 3)) : Prop :=
  (∀ k : Fin (m + 3), k ≠ 0 → k ≠ 1 → k ≠ 2 →
      ¬Sbtw ℝ (polygon.vertex 0) (polygon.vertex k) (polygon.vertex 2)) ∧
    ∀ k : Fin (m + 3), k ≠ 0 → k ≠ 1 →
      Disjoint
        {z : ℂ | Sbtw ℝ (polygon.vertex 0) z (polygon.vertex 2)}
        {z : ℂ | Sbtw ℝ (polygon.vertex k) z
          (polygon.vertex (k + 1))}


end StatMech.FrontierA
