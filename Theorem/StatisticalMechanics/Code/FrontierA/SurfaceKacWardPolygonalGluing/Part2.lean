/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardPolygonalGluing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardPolygonalDevelopment.Part3
import Def.StatisticalMechanics.Code.FrontierA.SurfaceKacWardPolygonalGluing.Part2
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierA

universe u v


namespace ClosedPolygonalGluingFlatSurfaceEmbedding

variable {g : Nat} {Cone : Type v} [Fintype Cone] [DecidableEq Cone]
  {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]


theorem developedTurnLift_constructed
    (embedding : ClosedPolygonalGluingFlatSurfaceEmbedding g Cone G)
    {root : V} (p : G.Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    forall k : Fin p.darts.length,
      (embedding.angle (kwGraphCycleDartLoop p (k + 1)) -
          embedding.angle (kwGraphCycleDartLoop p k)).toReal =
        (((Complex.arg ((embedding.developedPolygon p hp).edgeVector (k + 1)) :
            Real.Angle) -
          (Complex.arg ((embedding.developedPolygon p hp).edgeVector k) :
            Real.Angle)).toReal) +
        (embedding.chartTransitionIndex p k : Real) * (2 * Real.pi) := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  intro k
  simpa [chartTransitionIndex, hp] using embedding.developedTurnLift p hp k


end ClosedPolygonalGluingFlatSurfaceEmbedding
end StatMech.FrontierA
