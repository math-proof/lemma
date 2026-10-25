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
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffield.Part7
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


theorem PeriodicPlaneEmbedding.continuous_rectRestrict
    (E : PeriodicPlaneEmbedding P) (a b c d : ℝ) :
    Continuous (E.rectRestrict a b c d) :=
  continuous_pi fun e => continuous_apply (Sym2.map Subtype.val e)


theorem PeriodicPlaneEmbedding.openRectWalk_edge_open
    (E : PeriodicPlaneEmbedding P) {a b c d : ℝ}
    {omega : ConfigSpace (Sym2 V)}
    {x y : E.RectVertex a b c d}
    (p : (FK.openSub (E.rectGraph a b c d)
      (E.rectRestrict a b c d omega)).Walk x y)
    {u v : V}
    (huv : s(u, v) ∈
      (p.map (E.openRectHom a b c d
        (E.rectRestrict a b c d omega))).edges) :
    omega s(u, v) = true := by
  rw [SimpleGraph.Walk.edges_map] at huv
  obtain ⟨e, he, hmap⟩ := List.mem_map.mp huv
  induction e using Sym2.inductionOn with
  | _ r s =>
      have hrs := p.adj_of_mem_edges he
      rw [FK.openSub_adj] at hrs
      simp only [PeriodicPlaneEmbedding.rectRestrict,
        PeriodicPlaneEmbedding.openRectHom, Sym2.map_mk] at hrs hmap
      rw [← hmap]
      exact hrs.2


theorem PeriodicPlaneEmbedding.mem_openRectWalkArc_range
    (E : PeriodicPlaneEmbedding P) {a b c d : ℝ}
    {omega : ConfigSpace (Sym2 V)}
    {x y : E.RectVertex a b c d}
    (p : (FK.openSub (E.rectGraph a b c d)
      (E.rectRestrict a b c d omega)).Walk x y)
    (hp : ¬ (p.map (E.openRectHom a b c d
      (E.rectRestrict a b c d omega))).Nil)
    {q : ℂ}
    (hq : q ∈ Set.range (E.walkArc
      (p.map (E.openRectHom a b c d
        (E.rectRestrict a b c d omega))))) :
    ∃ u v : V, ∃ huv : P.graph.Adj u v,
      omega s(u, v) = true ∧ q ∈ Set.range (E.edgeArc huv) := by
  obtain ⟨u, v, huv, hedge, hqedge⟩ :=
    E.mem_walkArc_range_of_not_nil _ hp hq
  exact ⟨u, v, huv, E.openRectWalk_edge_open p hedge, hqedge⟩

end StatMech.FK.PeriodicPlanar
