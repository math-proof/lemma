/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCoverage.Part3
import Theorem.StatisticalMechanics.Code.FK.ContinuousRectangleCrossing.Part9
import Theorem.StatisticalMechanics.Code.Foundations.Ergodicity.Part2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffield.Part8
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


theorem PeriodicPlaneEmbedding.rectLeftBoundary_coord_lt
    (E : PeriodicPlaneEmbedding P) {B a b c d : ℝ}
    (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
    {x : E.RectVertex a b c d} (hx : E.rectLeftBoundary a b c d x) :
    E.vertexCoord x.1 0 < a + B := by
  obtain ⟨y, hxy, hy⟩ := hx
  have hd := hB hxy (1 : unitInterval) (0 : Fin 2)
  have heq : E.coordinates (E.edgeArc hxy (1 : unitInterval) - E.vertex x.1) 0 =
      E.vertexCoord y 0 - E.vertexCoord x.1 0 := by
    rw [Path.target]
    simp [PeriodicPlaneEmbedding.vertexCoord, map_sub]
  rw [heq] at hd
  have hd' := abs_le.mp hd
  linarith

theorem PeriodicPlaneEmbedding.rectRightBoundary_coord_gt
    (E : PeriodicPlaneEmbedding P) {B a b c d : ℝ}
    (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
    {x : E.RectVertex a b c d} (hx : E.rectRightBoundary a b c d x) :
    b - B < E.vertexCoord x.1 0 := by
  obtain ⟨y, hxy, hy⟩ := hx
  have hd := hB hxy (1 : unitInterval) (0 : Fin 2)
  have heq : E.coordinates (E.edgeArc hxy (1 : unitInterval) - E.vertex x.1) 0 =
      E.vertexCoord y 0 - E.vertexCoord x.1 0 := by
    rw [Path.target]
    simp [PeriodicPlaneEmbedding.vertexCoord, map_sub]
  rw [heq] at hd
  have hd' := abs_le.mp hd
  linarith

theorem PeriodicPlaneEmbedding.rectBottomBoundary_coord_lt
    (E : PeriodicPlaneEmbedding P) {B a b c d : ℝ}
    (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
    {x : E.RectVertex a b c d} (hx : E.rectBottomBoundary a b c d x) :
    E.vertexCoord x.1 1 < c + B := by
  obtain ⟨y, hxy, hy⟩ := hx
  have hd := hB hxy (1 : unitInterval) (1 : Fin 2)
  have heq : E.coordinates (E.edgeArc hxy (1 : unitInterval) - E.vertex x.1) 1 =
      E.vertexCoord y 1 - E.vertexCoord x.1 1 := by
    rw [Path.target]
    simp [PeriodicPlaneEmbedding.vertexCoord, map_sub]
  rw [heq] at hd
  have hd' := abs_le.mp hd
  linarith

theorem PeriodicPlaneEmbedding.rectTopBoundary_coord_gt
    (E : PeriodicPlaneEmbedding P) {B a b c d : ℝ}
    (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
    {x : E.RectVertex a b c d} (hx : E.rectTopBoundary a b c d x) :
    d - B < E.vertexCoord x.1 1 := by
  obtain ⟨y, hxy, hy⟩ := hx
  have hd := hB hxy (1 : unitInterval) (1 : Fin 2)
  have heq : E.coordinates (E.edgeArc hxy (1 : unitInterval) - E.vertex x.1) 1 =
      E.vertexCoord y 1 - E.vertexCoord x.1 1 := by
    rw [Path.target]
    simp [PeriodicPlaneEmbedding.vertexCoord, map_sub]
  rw [heq] at hd
  have hd' := abs_le.mp hd
  linarith


end StatMech.FK.PeriodicPlanar
