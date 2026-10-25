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
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardFinitePolygonEar.Part4


namespace StatMech.FrontierA

def KWFiniteSimplePolygon.edgeVector {n : ℕ} [NeZero n]
    (polygon : KWFiniteSimplePolygon n) (i : Fin n) : ℂ :=
  polygon.vertex (i + 1) - polygon.vertex i


def KWFiniteSimplePolygon.edgeList {n : ℕ} [NeZero n]
    (polygon : KWFiniteSimplePolygon n) : List ℂ :=
  List.ofFn polygon.edgeVector


noncomputable def KWFiniteSimplePolygon.rotate
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n) (r : Fin n) :
    KWFiniteSimplePolygon n where
  vertex := fun i ↦ polygon.vertex (i + r)
  three_le := polygon.three_le
  vertex_injective := polygon.vertex_injective.comp
    (Equiv.addRight r).injective
  vertex_not_strictly_between := by
    intro i j hji hjsucc
    have hji' : j + r ≠ i + r := by
      intro h
      exact hji (add_right_cancel h)
    have hsucc (k : Fin n) : (k + 1) + r = (k + r) + 1 := by abel
    have hjsucc' : j + r ≠ (i + r) + 1 := by
      rw [← hsucc]
      intro h
      exact hjsucc (add_right_cancel h)
    change ¬Sbtw ℝ (polygon.vertex (i + r))
      (polygon.vertex (j + r)) (polygon.vertex (i + 1 + r))
    rw [hsucc]
    exact polygon.vertex_not_strictly_between (i + r) (j + r)
      hji' hjsucc'
  edgeInteriors_disjoint := by
    intro i j hij
    have hij' : i + r ≠ j + r := by
      intro h
      exact hij (add_right_cancel h)
    have hsucc (k : Fin n) : (k + 1) + r = (k + r) + 1 := by abel
    change Disjoint
      {z : ℂ | Sbtw ℝ (polygon.vertex (i + r)) z
        (polygon.vertex (i + 1 + r))}
      {z : ℂ | Sbtw ℝ (polygon.vertex (j + r)) z
        (polygon.vertex (j + 1 + r))}
    rw [hsucc i, hsucc j]
    exact polygon.edgeInteriors_disjoint (i + r) (j + r) hij'

end StatMech.FrontierA
