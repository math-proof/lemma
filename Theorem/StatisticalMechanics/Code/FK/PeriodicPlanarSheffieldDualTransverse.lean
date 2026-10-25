/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDualTransverse.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneJoinedArms.Part2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldDualTransverse
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


theorem PeriodicPlaneEmbedding.abs_vertexCoord_le_orbitBoxCoordinateBound
    (E : PeriodicPlaneEmbedding P) {n : Nat} {v : V}
    (hv : v ∈ P.orbitBox n) (i : Fin 2) :
    |E.vertexCoord v i| ≤ E.orbitBoxCoordinateBound n i := by
  classical
  unfold PeriodicPlaneEmbedding.orbitBoxCoordinateBound
  exact Finset.le_sup' (fun w => |E.vertexCoord w i|) hv


theorem PeriodicPlaneEmbedding.walkArc_abs_coord_le_of_support_orbitBox
    (E : PeriodicPlaneEmbedding P) {B : Real} (hB0 : 0 ≤ B)
    (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
    {n : Nat} {x y : V} (q : P.graph.Walk x y)
    (hq : ∀ v ∈ q.support, v ∈ P.orbitBox n) :
    ∀ (t : unitInterval) (i : Fin 2),
      |E.coordinates (E.walkArc q t) i| ≤
        E.orbitBoxCoordinateBound n i + B := by
  intro t i
  have hpoint : E.walkArc q t ∈ Set.range (E.walkArc q) := ⟨t, rfl⟩
  rcases E.mem_walkArc_range_cases q hpoint with hstart | hedge
  · have hx := E.abs_vertexCoord_le_orbitBoxCoordinateBound
      (hq x (by simp)) i
    change E.walkArc q t = E.vertex x at hstart
    rw [hstart]
    change |E.vertexCoord x i| ≤ E.orbitBoxCoordinateBound n i + B
    linarith
  · obtain ⟨u, v, huv, huvEdge, s, hs⟩ := hedge
    have hu := E.abs_vertexCoord_le_orbitBoxCoordinateBound
      (hq u (q.fst_mem_support_of_mem_edges huvEdge)) i
    have hlo := E.vertex_sub_le_edgeArc_coord hB huv s i
    have hhi := E.edgeArc_coord_le_vertex_add hB huv s i
    change E.edgeArc huv s = E.walkArc q t at hs
    rw [← hs]
    rw [abs_le]
    rw [abs_le] at hu
    constructor <;> linarith


end StatMech.FK.PeriodicPlanar
