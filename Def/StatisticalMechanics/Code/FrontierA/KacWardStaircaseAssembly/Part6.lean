/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardIncidentStairPatch.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStaircaseAssembly.Part5


namespace StatMech.FrontierA

open scoped NNReal

open Set


def KWStairParameterData.MeshWithin
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon) (r : NNReal) : Prop :=
  ∀ i : Fin n, ∀ k : Fin S,
    (data.parameter i k.succ - data.parameter i k.castSucc) *
      ‖polygon.edgeVector i‖ < r

end StatMech.FrontierA
