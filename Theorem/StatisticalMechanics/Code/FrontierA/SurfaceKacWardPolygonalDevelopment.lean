/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardPolygonalDevelopment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardMetricClosure.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveClosure
import Structure.StatisticalMechanics.Code.FrontierA.SurfaceKacWardPolygonalDevelopment
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierA

universe u v


namespace ClosedPolygonalFlatSurfaceGraphAtlas

variable {g : Nat} {Cone : Type v} [Fintype Cone] [DecidableEq Cone]
  {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]


theorem exists_developedPolygon_odd_winding
    (atlas : ClosedPolygonalFlatSurfaceGraphAtlas g Cone G)
    {root : V} (p : G.Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    ∃ winding : Int,
      (∑ k : Fin p.darts.length,
        ((Complex.arg ((atlas.developedPolygon p hp).edgeVector (k + 1)) :
            Real.Angle) -
          (Complex.arg ((atlas.developedPolygon p hp).edgeVector k) :
            Real.Angle)).toReal : Real) =
        (winding : Real) * (2 * Real.pi) ∧ Odd winding := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  let polygon := atlas.developedPolygon p hp
  let developedAngle : Fin p.darts.length -> Real.Angle := fun k =>
    Complex.arg (polygon.edgeVector k)
  obtain ⟨winding, hturn⟩ :=
    kw_totalPrincipalTurn_eq_int_mul_two_pi developedAngle id
  have hphaseVector := kwFiniteSimplePolygonPhaseSign_adaptive polygon
  rw [KWFiniteSimplePolygon.edgeList, kwVectorPhaseCycle_ofFn] at hphaseVector
  have hphase : kwLoopPhaseProduct
      (fun a b => kwAngleTurnPhase (developedAngle a) (developedAngle b)) id =
        -1 := by
    simpa only [kwVectorTurnPhase, Function.comp_def, id_eq] using hphaseVector
  have hodd := kw_odd_winding_of_angleTurnPhase_eq_neg_one
    developedAngle id winding hturn hphase
  exact ⟨winding, hturn, hodd⟩


end ClosedPolygonalFlatSurfaceGraphAtlas
end StatMech.FrontierA
