module
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPolygonTurning.Part2
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardFourSignMajority
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardHalfPlaneSegment
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardInteriorSideSplice
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAntipodalExclusion
public import Mathlib.Data.List.Rotate
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardFinitePolygonEar.Part9


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

def KWFiniteSimplePolygon.VertexOneDoubleWrapEar
    {m : ℕ} (polygon : KWFiniteSimplePolygon (m + 3)) : Prop :=
  let previous := polygon.edgeVector (-1)
  let incoming := polygon.edgeVector 0
  let outgoing := polygon.edgeVector 1
  let next := polygon.edgeVector 2
  let diagonal := incoming + outgoing
  polygon.VertexOneDiagonalIsClean ∧
    kwComplexCross incoming outgoing ≠ 0 ∧
    kwAngleTurnWrap (Complex.arg previous : Real.Angle)
      (Complex.arg incoming : Real.Angle)
      (Complex.arg diagonal : Real.Angle) ∧
    kwAngleTurnWrap (Complex.arg diagonal : Real.Angle)
      (Complex.arg outgoing : Real.Angle)
      (Complex.arg next : Real.Angle)


def KWFiniteSimplePolygon.VertexOneStrictParityEar
    {m : ℕ} (polygon : KWFiniteSimplePolygon (m + 3)) : Prop :=
  let previous := polygon.edgeVector (-1)
  let incoming := polygon.edgeVector 0
  let outgoing := polygon.edgeVector 1
  let next := polygon.edgeVector 2
  let diagonal := incoming + outgoing
  polygon.VertexOneDiagonalIsClean ∧
    kwComplexCross incoming outgoing ≠ 0 ∧
    ((kwAngleTurnNoWrap (Complex.arg previous : Real.Angle)
          (Complex.arg incoming : Real.Angle)
          (Complex.arg diagonal : Real.Angle) ∧
        kwAngleTurnNoWrap (Complex.arg diagonal : Real.Angle)
          (Complex.arg outgoing : Real.Angle)
          (Complex.arg next : Real.Angle)) ∨
      (kwAngleTurnWrap (Complex.arg previous : Real.Angle)
          (Complex.arg incoming : Real.Angle)
          (Complex.arg diagonal : Real.Angle) ∧
        kwAngleTurnWrap (Complex.arg diagonal : Real.Angle)
          (Complex.arg outgoing : Real.Angle)
          (Complex.arg next : Real.Angle)))


end StatMech.FrontierA
