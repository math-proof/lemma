/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardPolygonalGluing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardPolygonalDevelopment.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardPolygonalGluing
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierA

universe u v


structure ClosedPolygonalGluingFlatSurfaceEmbedding (g : Nat)
    (Cone : Type v) [Fintype Cone] [DecidableEq Cone]
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] where
  cellular : FiniteCellularGraphEmbedding G
  genus_eq : cellular.genus = g
  angle : G.Dart -> Real.Angle
  edgeClass : Sym2 V -> SurfaceHomology g
  degree_le_three : forall vertex, G.degree vertex <= 3
  angle_reverse : forall dart, angle dart.symm = angle dart + Real.pi
  transition_nonantipodal : forall dart next,
    G.DartAdj dart next -> dart.edge ≠ next.edge ->
      angle next - angle dart ≠ Real.pi
  disjoint_edge_intersection : forall edge other : Sym2 V,
    Disjoint edge.toFinset other.toFinset ->
      surfaceIntersection (edgeClass edge) (edgeClass other) = 0
  coneOrder : Cone -> Int
  coneOrder_odd : forall cone, Odd (coneOrder cone)
  developedConeSupport : forall {root : V}, G.Walk root root -> Finset Cone
  developedPolygon : forall {root : V} (p : G.Walk root root)
      (hp : p.IsCycle),
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    KWFiniteSimplePolygon p.darts.length
  

  coneAnchor : forall {root : V} (p : G.Walk root root) (hp : p.IsCycle),
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    {cone // cone ∈ developedConeSupport p} -> Fin p.darts.length
  

  regularChartPairIndex : forall {root : V}
      (p : G.Walk root root) (hp : p.IsCycle),
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    Fin p.darts.length -> Int
  

  developedTurnLift : forall {root : V}
      (p : G.Walk root root) (hp : p.IsCycle),
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    forall k : Fin p.darts.length,
      (angle (kwGraphCycleDartLoop p (k + 1)) -
          angle (kwGraphCycleDartLoop p k)).toReal =
        (((Complex.arg ((developedPolygon p hp).edgeVector (k + 1)) :
            Real.Angle) -
          (Complex.arg ((developedPolygon p hp).edgeVector k) :
            Real.Angle)).toReal) +
        ((surfaceWalkQuadraticIncrement edgeClass p k +
          2 * regularChartPairIndex p hp k +
          ∑ cone : {cone // cone ∈ developedConeSupport p},
            if coneAnchor p hp cone = k then coneOrder cone - 1 else 0 : Int) :
          Real) * (2 * Real.pi)

end StatMech.FrontierA
