/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardPolygonalDevelopment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardMetricClosure.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveClosure
import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardPolygonalDevelopment
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierA

universe u v


namespace ClosedPolygonalFlatSurfaceGraphAtlas

variable {g : Nat} {Cone : Type v} [Fintype Cone] [DecidableEq Cone]
  {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]


noncomputable def developedPolygonHalf
    (atlas : ClosedPolygonalFlatSurfaceGraphAtlas g Cone G)
    {root : V} (p : G.Walk root root) : Int := by
  classical
  exact if hp : p.IsCycle then
      Classical.choose
        ((atlas.exists_developedPolygon_odd_winding p hp).choose_spec.2)
    else 0

end ClosedPolygonalFlatSurfaceGraphAtlas
end StatMech.FrontierA
