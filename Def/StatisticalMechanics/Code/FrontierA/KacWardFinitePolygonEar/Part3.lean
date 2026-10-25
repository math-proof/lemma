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
import Structure.StatisticalMechanics.Code.FrontierA.KacWardFinitePolygonEar


namespace StatMech.FrontierA

def kwCyclicEdgeVector {n : ℕ} [NeZero n]
    (vertex : Fin n → ℂ) (i : Fin n) : ℂ :=
  vertex (i + 1) - vertex i


def kwCyclicEdgeList {n : ℕ} [NeZero n]
    (vertex : Fin n → ℂ) : List ℂ :=
  List.ofFn (kwCyclicEdgeVector vertex)


def kwRemoveVertexOne {n : ℕ} [NeZero n]
    (vertex : Fin (n + 1) → ℂ) : Fin n → ℂ :=
  fun i ↦ vertex ((1 : Fin (n + 1)).succAbove i)

end StatMech.FrontierA
