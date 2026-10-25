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
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardFinitePolygonEar.Part3


namespace StatMech.FrontierA

structure KWFiniteSimplePolygon (n : ℕ) [NeZero n] where
  vertex : Fin n → ℂ
  three_le : 3 ≤ n
  vertex_injective : Function.Injective vertex
  vertex_not_strictly_between : ∀ (i j : Fin n),
    j ≠ i → j ≠ i + 1 →
      ¬Sbtw ℝ (vertex i) (vertex j) (vertex (i + 1))
  edgeInteriors_disjoint : ∀ (i j : Fin n), i ≠ j →
    Disjoint
      {z : ℂ | Sbtw ℝ (vertex i) z (vertex (i + 1))}
      {z : ℂ | Sbtw ℝ (vertex j) z (vertex (j + 1))}


end StatMech.FrontierA
