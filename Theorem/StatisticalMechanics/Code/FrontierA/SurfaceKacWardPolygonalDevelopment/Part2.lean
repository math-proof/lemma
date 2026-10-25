/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardPolygonalDevelopment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardMetricClosure.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveClosure
import Def.StatisticalMechanics.Code.FrontierA.SurfaceKacWardPolygonalDevelopment
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierA

universe u v


namespace ClosedPolygonalFlatSurfaceGraphAtlas

variable {g : Nat} {Cone : Type v} [Fintype Cone] [DecidableEq Cone]
  {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]


theorem developedPolygon_winding_eq_two_mul_half_add_one
    (atlas : ClosedPolygonalFlatSurfaceGraphAtlas g Cone G)
    {root : V} (p : G.Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    let winding := Classical.choose
      (atlas.exists_developedPolygon_odd_winding p hp)
    winding = 2 * atlas.developedPolygonHalf p + 1 := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  dsimp only
  rw [developedPolygonHalf, dif_pos hp]
  exact Classical.choose_spec
    ((atlas.exists_developedPolygon_odd_winding p hp).choose_spec.2)


theorem developedGaussBonnet
    (atlas : ClosedPolygonalFlatSurfaceGraphAtlas g Cone G)
    {root : V} (p : G.Walk root root) (hp : p.IsCycle) :
    kwClosedWalkAngleRotationNumber atlas.angle p =
      1 + (surfaceBaseQuadraticParity
        (surfaceSubgraphHomology atlas.edgeClass p.edges.toFinset)).val +
      2 * (atlas.developedPolygonHalf p +
        atlas.chartRegularTurnCorrection p) +
      ∑ cone ∈ atlas.developedConeSupport p, (atlas.coneOrder cone - 1) := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  let polygon := atlas.developedPolygon p hp
  let developedAngle : Fin p.darts.length -> Real.Angle := fun k =>
    Complex.arg (polygon.edgeVector k)
  let winding := Classical.choose
    (atlas.exists_developedPolygon_odd_winding p hp)
  have hpolygonTurn :=
    (atlas.exists_developedPolygon_odd_winding p hp).choose_spec.1
  have hwinding : winding = 2 * atlas.developedPolygonHalf p + 1 := by
    simpa only using
      atlas.developedPolygon_winding_eq_two_mul_half_add_one p hp
  have hsurfaceTurn :=
    kwClosedWalkAngleRotationNumber_spec atlas.angle p hp
  have hlocal :
      (∑ k : Fin p.darts.length,
        (atlas.angle (kwGraphCycleDartLoop p (k + 1)) -
        atlas.angle (kwGraphCycleDartLoop p k)).toReal : Real) =
      (∑ k : Fin p.darts.length,
        ((Complex.arg (polygon.edgeVector (k + 1)) : Real.Angle) -
        (Complex.arg (polygon.edgeVector k) : Real.Angle)).toReal : Real) +
      (∑ k : Fin p.darts.length,
        (atlas.chartTransitionIndex p k : Real)) *
        (2 * Real.pi) := by
    calc
      _ = ∑ k, (((Complex.arg
            ((atlas.developedPolygon p hp).edgeVector (k + 1)) : Real.Angle) -
          (Complex.arg
            ((atlas.developedPolygon p hp).edgeVector k) : Real.Angle)).toReal +
          (atlas.chartTransitionIndex p k : Real) * (2 * Real.pi)) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact atlas.developedTurnLift p hp k
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_mul]
  have hrotationReal :
      (kwClosedWalkAngleRotationNumber atlas.angle p : Real) =
        (winding : Real) +
          (∑ k : Fin p.darts.length,
            atlas.chartTransitionIndex p k : Int) := by
    rw [hsurfaceTurn, hpolygonTurn] at hlocal
    push_cast
    nlinarith [Real.pi_pos]
  have hrotation :
      kwClosedWalkAngleRotationNumber atlas.angle p =
        winding + ∑ k : Fin p.darts.length,
          atlas.chartTransitionIndex p k := by
    exact_mod_cast hrotationReal
  have hindex := atlas.chartIndexGaussBonnet p hp
  rw [hrotation, hindex, hwinding]
  ring


end ClosedPolygonalFlatSurfaceGraphAtlas
end StatMech.FrontierA
