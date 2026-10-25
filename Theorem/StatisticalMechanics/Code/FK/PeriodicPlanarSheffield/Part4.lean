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
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffield.Part4
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


@[simp] theorem PeriodicPlaneEmbedding.walkArc_nil
    (E : PeriodicPlaneEmbedding P) (x : V) :
    E.walkArc (.nil : P.graph.Walk x x) = Path.refl _ := rfl

@[simp] theorem PeriodicPlaneEmbedding.walkArc_cons
    (E : PeriodicPlaneEmbedding P) {x y z : V}
    (hxy : P.graph.Adj x y) (p : P.graph.Walk y z) :
    E.walkArc (p.cons hxy) = (E.edgeArc hxy).trans (E.walkArc p) := rfl


theorem PeriodicPlaneEmbedding.mem_walkArc_range_cases
    (E : PeriodicPlaneEmbedding P) {x y : V} (p : P.graph.Walk x y)
    {q : ℂ} (hq : q ∈ Set.range (E.walkArc p)) :
    q = E.vertex x ∨
      ∃ u v : V, ∃ huv : P.graph.Adj u v,
        s(u, v) ∈ p.edges ∧ q ∈ Set.range (E.edgeArc huv) := by
  induction p with
  | @nil u =>
      left
      obtain ⟨t, rfl⟩ := hq
      rfl
  | @cons u v w huv p ih =>
      rw [PeriodicPlaneEmbedding.walkArc_cons, Path.trans_range] at hq
      rcases hq with hq | hq
      · right
        exact ⟨u, v, huv, by simp, hq⟩
      · rcases ih hq with hstart | hedge
        · right
          refine ⟨u, v, huv, by simp, ?_⟩
          refine ⟨1, ?_⟩
          simpa only [Path.target] using hstart.symm
        · obtain ⟨a, b, hab, habmem, hqedge⟩ := hedge
          right
          exact ⟨a, b, hab, by simp [habmem], hqedge⟩


theorem PeriodicPlaneEmbedding.mem_walkArc_range_of_not_nil
    (E : PeriodicPlaneEmbedding P) {x y : V} (p : P.graph.Walk x y)
    (hp : ¬ p.Nil) {q : ℂ} (hq : q ∈ Set.range (E.walkArc p)) :
    ∃ u v : V, ∃ huv : P.graph.Adj u v,
      s(u, v) ∈ p.edges ∧ q ∈ Set.range (E.edgeArc huv) := by
  rcases E.mem_walkArc_range_cases p hq with hstart | hedge
  · obtain ⟨v, huv, p', rfl⟩ := SimpleGraph.Walk.not_nil_iff.mp hp
    refine ⟨x, v, huv, by simp, ?_⟩
    refine ⟨0, ?_⟩
    simpa only [Path.source] using hstart.symm
  · exact hedge

theorem PeriodicPlaneEmbedding.walkArc_range_subset_expanded_planeRect
    (E : PeriodicPlaneEmbedding P) {B : ℝ}
    (hB0 : 0 ≤ B)
    (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
    {a b c d : ℝ} {x y : V} (p : P.graph.Walk x y)
    (hp : ∀ v, v ∈ p.support → E.vertex v ∈ E.planeRect a b c d) :
    Set.range (E.walkArc p) ⊆
      E.planeRect (a - B) (b + B) (c - B) (d + B) := by
  induction p with
  | @nil u =>
      intro q hq
      obtain ⟨t, rfl⟩ := hq
      rw [PeriodicPlaneEmbedding.walkArc_nil]
      simp only [Path.refl_apply]
      have hx := hp u (by simp)
      change a ≤ E.vertexCoord u 0 ∧ E.vertexCoord u 0 ≤ b ∧
        c ≤ E.vertexCoord u 1 ∧ E.vertexCoord u 1 ≤ d at hx
      change a - B ≤ E.vertexCoord u 0 ∧ E.vertexCoord u 0 ≤ b + B ∧
        c - B ≤ E.vertexCoord u 1 ∧ E.vertexCoord u 1 ≤ d + B
      rcases hx with ⟨hxa, hxb, hxc, hxd⟩
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  | @cons x y z hxy p ih =>
      rw [PeriodicPlaneEmbedding.walkArc_cons, Path.trans_range]
      intro q hq
      rcases hq with hq | hq
      · obtain ⟨t, rfl⟩ := hq
        exact E.edgeArc_mem_expanded_planeRect hB hxy
          (hp x (by simp)) t
      · exact ih (fun v hv => hp v (by simp [hv])) hq


end StatMech.FK.PeriodicPlanar
