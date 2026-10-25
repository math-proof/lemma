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
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardFinitePolygonEar.Part8


namespace StatMech.FrontierA

def KWFiniteSimplePolygon.VertexOnePhaseEar
    {m : ℕ} (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3)) : Prop :=
  let remaining := List.ofFn (fun i : Fin (m + 1) ↦
    polygon.edgeVector i.succ.succ)
  kwVectorTurnPhase (remaining.tail.getLast (by
        simp [remaining]; omega)) (polygon.edgeVector 0) *
      kwVectorTurnPhase (polygon.edgeVector 0) (polygon.edgeVector 1) *
      kwVectorTurnPhase (polygon.edgeVector 1)
        (remaining.head (by simp [remaining])) =
    kwVectorTurnPhase (remaining.tail.getLast (by
        simp [remaining]; omega))
          (polygon.edgeVector 0 + polygon.edgeVector 1) *
      kwVectorTurnPhase
        (polygon.edgeVector 0 + polygon.edgeVector 1)
        (remaining.head (by simp [remaining]))


def KWFiniteSimplePolygon.VertexOneCrossEar
    {m : ℕ} (polygon : KWFiniteSimplePolygon (m + 3)) : Prop :=
  kwComplexCross (polygon.edgeVector 0) (polygon.edgeVector 1) ≠ 0 ∧
    (Complex.arg (polygon.edgeVector 2) : Real.Angle) -
        (Complex.arg (polygon.edgeVector 1) : Real.Angle) ≠
      (Real.pi : Real.Angle) ∧
    ((0 < kwComplexCross (polygon.edgeVector (-1))
          (polygon.edgeVector 0) ∧
        0 < kwComplexCross (polygon.edgeVector (-1))
          (polygon.edgeVector 0 + polygon.edgeVector 1)) ∨
      (kwComplexCross (polygon.edgeVector (-1))
            (polygon.edgeVector 0) < 0 ∧
        kwComplexCross (polygon.edgeVector (-1))
            (polygon.edgeVector 0 + polygon.edgeVector 1) < 0)) ∧
    ((0 < kwComplexCross
          (polygon.edgeVector 0 + polygon.edgeVector 1)
          (polygon.edgeVector 1) ∧
        0 < kwComplexCross
          (polygon.edgeVector 0 + polygon.edgeVector 1)
          (polygon.edgeVector 2)) ∨
      (kwComplexCross
            (polygon.edgeVector 0 + polygon.edgeVector 1)
            (polygon.edgeVector 1) < 0 ∧
        kwComplexCross
            (polygon.edgeVector 0 + polygon.edgeVector 1)
            (polygon.edgeVector 2) < 0))


def KWFiniteSimplePolygon.VertexOneGeometricEar
    {m : ℕ} (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3)) : Prop :=
  polygon.VertexOneDiagonalIsClean ∧ polygon.VertexOnePhaseEar hm


def KWFiniteSimplePolygon.VertexOneAlignedSideEar
    {m : ℕ} (polygon : KWFiniteSimplePolygon (m + 3)) : Prop :=
  polygon.VertexOneDiagonalIsClean ∧
    kwComplexCross (polygon.edgeVector 0) (polygon.edgeVector 1) ≠ 0 ∧
    ((0 < kwComplexCross (polygon.edgeVector 0) (polygon.edgeVector 1) ∧
          0 < kwComplexCross (polygon.edgeVector (-1))
            (polygon.edgeVector 0 + polygon.edgeVector 1)) ∨
      (kwComplexCross (polygon.edgeVector 0) (polygon.edgeVector 1) < 0 ∧
          kwComplexCross (polygon.edgeVector (-1))
            (polygon.edgeVector 0 + polygon.edgeVector 1) < 0)) ∧
    ((0 < kwComplexCross (polygon.edgeVector 0) (polygon.edgeVector 1) ∧
          0 < kwComplexCross
            (polygon.edgeVector 0 + polygon.edgeVector 1)
            (polygon.edgeVector 2)) ∨
      (kwComplexCross (polygon.edgeVector 0) (polygon.edgeVector 1) < 0 ∧
          kwComplexCross
            (polygon.edgeVector 0 + polygon.edgeVector 1)
            (polygon.edgeVector 2) < 0))


def kwAngleTurnWrap (a b c : Real.Angle) : Prop :=
  b - a ≠ (Real.pi : Real.Angle) ∧
    c - b ≠ (Real.pi : Real.Angle) ∧
    c - a ≠ (Real.pi : Real.Angle) ∧
    (b - a).sign = (c - b).sign ∧
    (b - a).sign ≠ (c - a).sign


def kwAngleTurnNoWrap (a b c : Real.Angle) : Prop :=
  b - a ≠ (Real.pi : Real.Angle) ∧
    c - b ≠ (Real.pi : Real.Angle) ∧
    ((b - a).sign ≠ (c - b).sign ∨
      (b - a).sign = (c - a).sign)


end StatMech.FrontierA
