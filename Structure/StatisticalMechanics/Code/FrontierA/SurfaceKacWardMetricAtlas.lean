/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardMetricAtlas.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardAtlas.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPolygonGlobalReduction.Part6
import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardMetricAtlas.Part2
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierA

universe u v


structure ClosedMetricFlatSurfaceGraphAtlas (g : Nat)
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
  regularTurnCorrection : forall {root : V}, G.Walk root root -> Int
  developedConeSupport : forall {root : V}, G.Walk root root -> Finset Cone
  developedGaussBonnet : forall {root : V}
      (p : G.Walk root root) (hp : p.IsCycle),
    kwClosedWalkAngleRotationNumber angle p =
      1 + (surfaceBaseQuadraticParity
        (surfaceSubgraphHomology edgeClass p.edges.toFinset)).val +
      2 * regularTurnCorrection p +
      ∑ cone ∈ developedConeSupport p, (coneOrder cone - 1)

end StatMech.FrontierA
