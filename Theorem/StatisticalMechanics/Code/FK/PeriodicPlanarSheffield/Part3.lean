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
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffield.Part3
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


theorem PeriodicPlaneEmbedding.edgeArc_mem_expanded_planeRect
    (E : PeriodicPlaneEmbedding P) {B : ℝ}
    (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
    {a b c d : ℝ} {x y : V} (hxy : P.graph.Adj x y)
    (hx : E.vertex x ∈ E.planeRect a b c d) (t) :
    E.edgeArc hxy t ∈ E.planeRect (a - B) (b + B) (c - B) (d + B) := by
  have hcoord (i : Fin 2) :
      E.coordinates (E.edgeArc hxy t - E.vertex x) i =
        E.coordinates (E.edgeArc hxy t) i - E.vertexCoord x i := by
    simp [PeriodicPlaneEmbedding.vertexCoord, map_sub]
  have h₀ := hB hxy t (0 : Fin 2)
  have h₁ := hB hxy t (1 : Fin 2)
  rw [hcoord] at h₀ h₁
  have h₀' := (abs_le.mp h₀)
  have h₁' := (abs_le.mp h₁)
  change a ≤ E.vertexCoord x 0 ∧ E.vertexCoord x 0 ≤ b ∧
    c ≤ E.vertexCoord x 1 ∧ E.vertexCoord x 1 ≤ d at hx
  change a - B ≤ E.coordinates (E.edgeArc hxy t) 0 ∧
    E.coordinates (E.edgeArc hxy t) 0 ≤ b + B ∧
    c - B ≤ E.coordinates (E.edgeArc hxy t) 1 ∧
    E.coordinates (E.edgeArc hxy t) 1 ≤ d + B
  rcases hx with ⟨hxa, hxb, hxc, hxd⟩
  constructor
  · exact le_trans (sub_le_sub_right hxa B) (by linarith [h₀'.1])
  constructor
  · have ht : E.coordinates (E.edgeArc hxy t) 0 ≤
        E.vertexCoord x 0 + B := by linarith [h₀'.2]
    linarith [ht, hxb]
  constructor
  · exact le_trans (sub_le_sub_right hxc B) (by linarith [h₁'.1])
  · have ht : E.coordinates (E.edgeArc hxy t) 1 ≤
        E.vertexCoord x 1 + B := by linarith [h₁'.2]
    linarith [ht, hxd]

theorem PeriodicPlaneEmbedding.edgeArc_coord_le_vertex_add
    (E : PeriodicPlaneEmbedding P) {B : ℝ}
    (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
    {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2) :
    E.coordinates (E.edgeArc hxy t) i ≤ E.vertexCoord x i + B := by
  change E.coordinates (E.edgeArc hxy t) i ≤
    E.coordinates (E.vertex x) i + B
  have h := (abs_le.mp (hB hxy t i)).2
  simp only [map_sub, Pi.sub_apply] at h
  linarith

theorem PeriodicPlaneEmbedding.vertex_sub_le_edgeArc_coord
    (E : PeriodicPlaneEmbedding P) {B : ℝ}
    (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
    {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2) :
    E.vertexCoord x i - B ≤ E.coordinates (E.edgeArc hxy t) i := by
  change E.coordinates (E.vertex x) i - B ≤
    E.coordinates (E.edgeArc hxy t) i
  have h := (abs_le.mp (hB hxy t i)).1
  simp only [map_sub, Pi.sub_apply] at h
  linarith


end StatMech.FK.PeriodicPlanar
