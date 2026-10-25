/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardIncidentStairPatch.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStaircaseAssembly.Part3


namespace StatMech.FrontierA

open scoped NNReal

open Set


noncomputable def KWStairParameterData.base
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    (i : Fin n) (k : Fin (S + 1)) : ℂ :=
  AffineMap.lineMap (polygon.vertex i) (polygon.vertex (i + 1))
    (data.parameter i k)

noncomputable def KWStairParameterData.corner
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    (i : Fin n) (k : Fin S) : ℂ :=
  data.base i k.castSucc +
    (data.parameter i k.succ - data.parameter i k.castSucc) *
      kwHorizontalPart (polygon.edgeVector i)

noncomputable def KWStairParameterData.localVertex
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    (i : Fin n) (l : Fin (2 * S)) : ℂ :=
  if l.val % 2 = 0 then
    data.base i (kwStairSliceIndex l).castSucc
  else
    data.corner i (kwStairSliceIndex l)

end StatMech.FrontierA
