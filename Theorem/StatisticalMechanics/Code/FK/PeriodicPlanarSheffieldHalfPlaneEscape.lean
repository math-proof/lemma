/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneEscape.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlane.Part4
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


theorem PeriodicGraph.mem_connectedWithinSet_of_walk
    (P : PeriodicGraph V) {omega : ConfigSpace (Sym2 V)}
    {A : Set V} {x y : V} (p : (P.openSubgraph omega).Walk x y)
    (hp : ∀ v ∈ p.support, v ∈ A) :
    omega ∈ P.connectedWithinSet A x y := by
  refine ⟨p.support.tail, ?_, ?_, ?_⟩
  · rw [p.cons_tail_support]
    exact p.isChain_adj_support
  · simpa only [p.cons_tail_support] using p.getLast_support
  · rwa [p.cons_tail_support]


theorem PeriodicPlaneEmbedding.exists_boundary_walk_of_walk_to_left
    (E : PeriodicPlaneEmbedding P) (omega : ConfigSpace (Sym2 V)) (r : ℝ)
    {x y : V} (p : (P.openSubgraph omega).Walk x y)
    (hx : x ∈ E.rightHalfPlaneVertices r)
    (hy : y ∉ E.rightHalfPlaneVertices r) :
    ∃ b ∈ E.rightHalfPlaneBoundaryVertices r,
      ∃ q : (P.openSubgraph omega).Walk x b,
        ∀ v ∈ q.support, v ∈ E.rightHalfPlaneVertices r := by
  induction p with
  | nil => exact (hy hx).elim
  | @cons x z y hxz p ih =>
      by_cases hz : z ∈ E.rightHalfPlaneVertices r
      · obtain ⟨b, hb, q, hq⟩ := ih hz hy
        refine ⟨b, hb, q.cons hxz, ?_⟩
        intro v hv
        rw [SimpleGraph.Walk.support_cons] at hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact hx
        · exact hq v hv
      · refine ⟨x, ?_, .nil, ?_⟩
        · refine ⟨hx, z, hxz.1, ?_⟩
          exact lt_of_not_ge hz
        · simpa using hx


theorem PeriodicPlaneEmbedding.connectedWithin_rightHalfPlane_boundary_of_reachable
    (E : PeriodicPlaneEmbedding P) (omega : ConfigSpace (Sym2 V)) (r : ℝ)
    {x y : V} (hx : x ∈ E.rightHalfPlaneVertices r)
    (hy : y ∉ E.rightHalfPlaneVertices r)
    (hxy : y ∈ P.cluster omega x) :
    ∃ b ∈ E.rightHalfPlaneBoundaryVertices r,
      omega ∈ P.connectedWithinSet (E.rightHalfPlaneVertices r) x b := by
  obtain ⟨p⟩ := hxy
  obtain ⟨b, hb, q, hq⟩ :=
    E.exists_boundary_walk_of_walk_to_left omega r p hx hy
  exact ⟨b, hb, P.mem_connectedWithinSet_of_walk q hq⟩


end StatMech.FK.PeriodicPlanar
