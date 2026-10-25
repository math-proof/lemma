/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardMetricClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardMetricAtlas.Part4
import Def.StatisticalMechanics.Code.FrontierA.SurfaceKacWardMetricClosure.Part2
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierA

universe u v

namespace ClosedMetricFlatSurfaceGraphAtlas

variable {g : Nat} {Cone : Type v} [Fintype Cone] [DecidableEq Cone]
  {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]


theorem toClosedFlatSurfaceGraphAtlas_admissible
    (atlas : ClosedMetricFlatSurfaceGraphAtlas g Cone G) :
    atlas.toClosedFlatSurfaceGraphAtlas.AdmissibleConeAngles := by
  intro root p hp
  exact atlas.admissibleConeAngles p hp


theorem simple_cycle_holonomy
    (atlas : ClosedMetricFlatSurfaceGraphAtlas g Cone G)
    {root : V} (p : G.Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    kwLoopPhaseProduct atlas.phase (kwGraphCycleDartLoop p) =
      -(surfaceBaseCycleCoefficient atlas.edgeClass p.edges.toFinset) := by
  exact atlas.toClosedFlatSurfaceGraphAtlas.simple_cycle_holonomy
    atlas.toClosedFlatSurfaceGraphAtlas_admissible p hp


end ClosedMetricFlatSurfaceGraphAtlas
end StatMech.FrontierA
