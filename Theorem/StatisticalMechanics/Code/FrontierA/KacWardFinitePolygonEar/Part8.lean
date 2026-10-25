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
import Def.StatisticalMechanics.Code.FrontierA.KacWardFinitePolygonEar.Part7


namespace StatMech.FrontierA

@[simp] theorem KWFiniteSimplePolygon.removeVertexOne_vertex
    {m : ℕ} (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3))
    (hsimple : polygon.VertexOneRemovalIsSimple) :
    (polygon.removeVertexOne hm hsimple).vertex =
      kwRemoveVertexOne polygon.vertex := rfl

theorem KWFiniteSimplePolygon.removeVertexOne_edgeList
    {m : ℕ} (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3))
    (hsimple : polygon.VertexOneRemovalIsSimple) :
    (polygon.removeVertexOne hm hsimple).edgeList =
      (polygon.edgeVector 0 + polygon.edgeVector 1) ::
        List.ofFn (fun i : Fin (m + 1) ↦ polygon.edgeVector i.succ.succ) := by
  rw [KWFiniteSimplePolygon.edgeList_eq_cyclic]
  change kwCyclicEdgeList (kwRemoveVertexOne polygon.vertex) = _
  simpa only [KWFiniteSimplePolygon.edgeVector_eq_cyclic] using
    kwCyclicEdgeList_removeVertexOne polygon.vertex


end StatMech.FrontierA
