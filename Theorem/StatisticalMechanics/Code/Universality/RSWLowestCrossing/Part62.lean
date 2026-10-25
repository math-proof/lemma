/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.Exploration.Part5
import Theorem.StatisticalMechanics.Code.Percolation.OffClusterIndep.Part4
import Theorem.StatisticalMechanics.Code.Percolation.SurfaceReassembly
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.Inequalities.Harris
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.ClosedContourSeparation.Part2
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Universality.CrossingTranslationInvariance.Part3
import Theorem.StatisticalMechanics.Code.Universality.ConnectedRCoastClose.Part13
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part61
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_rightSafeTraceGraph_le_traceGraph {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) :
    rlc_rightSafeTraceGraph gamma delta ≤
      rlc_rightTraceGraph gamma delta := by
  intro u v huv
  exact ⟨huv.1, huv.2.1⟩


theorem rlc_jointBottomTraceBoundary_adj_safeTraceGraph {n : ℤ}
    (hn : 0 < n) (gamma delta : RlcRightDiagonalPath n)
    {u v : rect 0 (2 * n) (-n) n}
    (hu : (u : Site 2) ∈ rlc_jointBottomTraceBoundary gamma delta)
    (hv : (v : Site 2) ∈ rlc_jointBottomTraceBoundary gamma delta)
    (he : s((u : Site 2), (v : Site 2)) ∈
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges delta.1)
    (hadj : ((hypercubicLattice 2).induce
      (rect 0 (2 * n) (-n) n)).Adj u v) :
    (rlc_rightSafeTraceGraph gamma delta).Adj u v :=
  ⟨hadj, he, rlc_jointBottomTraceBoundary_safe hn gamma delta hu,
    rlc_jointBottomTraceBoundary_safe hn gamma delta hv⟩


theorem rlc_jointBottomTraceBoundary_walk_safe {n : ℤ}
    (hn : 0 < n) (gamma delta : RlcRightDiagonalPath n)
    {x y : rect 0 (2 * n) (-n) n}
    (w : (rlc_rightTraceGraph gamma delta).Walk x y)
    (hboundary : ∀ z ∈ w.support,
      (z : Site 2) ∈ rlc_jointBottomTraceBoundary gamma delta) :
    (rlc_rightSafeTraceGraph gamma delta).Reachable x y := by
  refine ⟨w.transfer (rlc_rightSafeTraceGraph gamma delta) ?_⟩
  intro e he
  induction e using Sym2.inductionOn with
  | _ u v =>
      have huv := w.adj_of_mem_edges he
      exact rlc_jointBottomTraceBoundary_adj_safeTraceGraph hn gamma delta
        (hboundary u (w.fst_mem_support_of_mem_edges he))
        (hboundary v (w.snd_mem_support_of_mem_edges he)) huv.2 huv.1


theorem rlc_jointBottomTraceFrontier_adj_safeTraceGraph {n : ℤ}
    (hn : 0 < n) (gamma delta : RlcRightDiagonalPath n)
    {u v : rect 0 (2 * n) (-n) n}
    (hu : (u : Site 2) ∈ rlc_jointBottomTraceFrontier gamma delta)
    (hv : (v : Site 2) ∈ rlc_jointBottomTraceFrontier gamma delta)
    (he : s((u : Site 2), (v : Site 2)) ∈
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges delta.1)
    (hadj : ((hypercubicLattice 2).induce
      (rect 0 (2 * n) (-n) n)).Adj u v) :
    (rlc_rightSafeTraceGraph gamma delta).Adj u v :=
  ⟨hadj, he, rlc_jointBottomTraceFrontier_safe hn gamma delta hu,
    rlc_jointBottomTraceFrontier_safe hn gamma delta hv⟩


theorem rlc_jointBottomTraceFrontier_walk_safe {n : ℤ}
    (hn : 0 < n) (gamma delta : RlcRightDiagonalPath n)
    {x y : rect 0 (2 * n) (-n) n}
    (w : (rlc_rightTraceGraph gamma delta).Walk x y)
    (hfrontier : ∀ z ∈ w.support,
      (z : Site 2) ∈ rlc_jointBottomTraceFrontier gamma delta) :
    (rlc_rightSafeTraceGraph gamma delta).Reachable x y := by
  refine ⟨w.transfer (rlc_rightSafeTraceGraph gamma delta) ?_⟩
  intro e he
  induction e using Sym2.inductionOn with
  | _ u v =>
      have huv := w.adj_of_mem_edges he
      exact rlc_jointBottomTraceFrontier_adj_safeTraceGraph hn gamma delta
        (hfrontier u (w.fst_mem_support_of_mem_edges he))
        (hfrontier v (w.snd_mem_support_of_mem_edges he)) huv.2 huv.1


theorem rlc_rightSafeTraceGraph_reachable_iff_traceWalk_safe {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    {u v : rect 0 (2 * n) (-n) n}
    (hu : (u : Site 2) ∉ rlc_rightUpperUnionSet gamma delta) :
    (rlc_rightSafeTraceGraph gamma delta).Reachable u v ↔
      ∃ p : (rlc_rightTraceGraph gamma delta).Walk u v,
        ∀ z ∈ p.support,
          (z : Site 2) ∉ rlc_rightUpperUnionSet gamma delta := by
  constructor
  · rintro ⟨p⟩
    let q := p.mapLe (rlc_rightSafeTraceGraph_le_traceGraph gamma delta)
    have hsafe : ∀ z ∈ p.support,
        (z : Site 2) ∉ rlc_rightUpperUnionSet gamma delta := by
      intro z hz
      induction p with
      | nil =>
          rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
          exact hz ▸ hu
      | @cons a b c hab p ih =>
          rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
          rcases hz with rfl | hz
          · exact hab.2.2.1
          · exact ih hab.2.2.2 hz
    refine ⟨q, ?_⟩
    intro z hz
    have hz' : z ∈ p.support := by
      simpa [q, SimpleGraph.Walk.support_mapLe_eq_support] using hz
    exact hsafe z hz'
  · rintro ⟨p, hp⟩
    refine ⟨p.transfer (rlc_rightSafeTraceGraph gamma delta) ?_⟩
    intro e he
    induction e using Sym2.inductionOn with
    | _ a b =>
        have hab := p.adj_of_mem_edges he
        have ha : a ∈ p.support := p.fst_mem_support_of_mem_edges he
        have hb : b ∈ p.support := p.snd_mem_support_of_mem_edges he
        exact ⟨hab.1, hab.2, hp a ha, hp b hb⟩


end Universality
end StatMech
