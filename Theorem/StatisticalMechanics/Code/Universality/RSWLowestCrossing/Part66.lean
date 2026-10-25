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
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part65
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_commonRightPathVertex_not_upperUnion {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) {z : Site 2}
    (hzGamma : z ∈ rlc_pathVertices gamma.1)
    (hzDelta : z ∈ rlc_pathVertices delta.1) :
    z ∉ rlc_rightUpperUnionSet gamma delta := by
  rintro (hzTopGamma | hzTopDelta)
  · exact (Set.disjoint_left.mp
      (rlc_strictTopSet_disjoint_path gamma)) hzTopGamma hzGamma
  · exact (Set.disjoint_left.mp
      (rlc_strictTopSet_disjoint_path delta)) hzTopDelta hzDelta


theorem rlc_walk_pred_first_exit {V : Type*} {G : SimpleGraph V} {x y : V}
    (w : G.Walk x y) (P : V → Prop) (hx : P x) (hy : ¬ P y) :
    ∃ u v, s(u, v) ∈ w.edges ∧ P u ∧ ¬ P v := by
  classical
  induction w with
  | nil => exact False.elim (hy hx)
  | @cons a b c hab p ih =>
      by_cases hb : P b
      · obtain ⟨u, v, huv, hu, hv⟩ := ih hb hy
        exact ⟨u, v, by simp [huv], hu, hv⟩
      · exact ⟨a, b, by simp, hx, hb⟩


theorem rlc_walk_pred_first_exit_prefix {V : Type*} {G : SimpleGraph V}
    {x y : V} (w : G.Walk x y) (P : V → Prop) (hx : P x) (hy : ¬ P y) :
    ∃ (u v : V) (q : G.Walk x u),
      G.Adj u v ∧ s(u, v) ∈ w.edges ∧
      (∀ e ∈ q.edges, e ∈ w.edges) ∧
      (∀ z ∈ q.support, P z) ∧ ¬ P v := by
  classical
  induction w with
  | nil => exact False.elim (hy hx)
  | @cons a b c hab p ih =>
      by_cases hb : P b
      · obtain ⟨u, v, q, huv, huvEdge, hqEdges, hqSafe, hv⟩ := ih hb hy
        refine ⟨u, v, .cons hab q, huv, by simp [huvEdge], ?_, ?_, hv⟩
        · intro e he
          simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
          rcases he with rfl | he
          · simp
          · simp [hqEdges e he]
        · intro z hz
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
          rcases hz with rfl | hz
          · exact hx
          · exact hqSafe z hz
      · refine ⟨a, b, .nil, hab, by simp, ?_, ?_, hb⟩
        · intro e he
          simp at he
        · intro z hz
          rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
          exact hz ▸ hx


theorem rlc_rightTrace_switchPoint_of_enter_upperUnion {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) {u v : Site 2}
    (he : s(u, v) ∈ rlc_pathEdges gamma.1)
    (hu : u ∉ rlc_rightUpperUnionSet gamma delta)
    (hv : v ∈ rlc_rightUpperUnionSet gamma delta) :
    u ∈ rlc_pathVertices gamma.1 ∧
      u ∈ rlc_pathVertices delta.1 := by
  have hends := rlc_pathEdge_endpoints_mem_vertices gamma.1 he
  refine ⟨hends.1, ?_⟩
  rcases hv with hvGamma | hvDelta
  · exact False.elim ((Set.disjoint_left.mp
      (rlc_strictTopSet_disjoint_path gamma)) hvGamma hends.2)
  · exact rlc_rightPathEdge_enter_strictTop_common
      gamma delta he (fun h => hu (Or.inr h)) hvDelta


theorem rlc_rightTrace_switchPoint_of_enter_upperUnion' {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) {u v : Site 2}
    (he : s(u, v) ∈ rlc_pathEdges delta.1)
    (hu : u ∉ rlc_rightUpperUnionSet gamma delta)
    (hv : v ∈ rlc_rightUpperUnionSet gamma delta) :
    u ∈ rlc_pathVertices gamma.1 ∧
      u ∈ rlc_pathVertices delta.1 := by
  have h := rlc_rightTrace_switchPoint_of_enter_upperUnion
    delta gamma he (by simpa [rlc_rightUpperUnionSet, Set.union_comm] using hu)
      (by simpa [rlc_rightUpperUnionSet, Set.union_comm] using hv)
  exact ⟨h.2, h.1⟩


theorem rlc_rightTrace_common_switch_before_unsafe_end {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    (hstart : (gamma.1.1 : Site 2) ∉
      rlc_rightUpperUnionSet gamma delta)
    (hend : (gamma.1.2.1 : Site 2) ∈
      rlc_rightUpperUnionSet gamma delta) :
    ∃ u v : rect 0 (2 * n) (-n) n,
      s((u : Site 2), (v : Site 2)) ∈ rlc_pathEdges gamma.1 ∧
      (u : Site 2) ∉ rlc_rightUpperUnionSet gamma delta ∧
      (v : Site 2) ∈ rlc_rightUpperUnionSet gamma delta ∧
      (u : Site 2) ∈ rlc_pathVertices gamma.1 ∧
      (u : Site 2) ∈ rlc_pathVertices delta.1 := by
  classical
  let p := gamma.1.2.2.1
  obtain ⟨u, v, huv, hu, hv⟩ := rlc_walk_pred_first_exit p
    (fun z => (z : Site 2) ∉ rlc_rightUpperUnionSet gamma delta)
    (by simpa [p] using hstart) (by simpa [p] using hend)
  have he : s((u : Site 2), (v : Site 2)) ∈
      rlc_pathEdges gamma.1 := by
    simp only [rlc_pathEdges, Finset.mem_image, List.mem_toFinset]
    exact ⟨s(u, v), huv, rfl⟩
  have hcommon := rlc_rightTrace_switchPoint_of_enter_upperUnion
    gamma delta he hu (not_not.mp hv)
  exact ⟨u, v, he, hu, not_not.mp hv, hcommon.1, hcommon.2⟩


theorem rlc_rightTrace_common_switch_before_unsafe_end' {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    (hstart : (delta.1.1 : Site 2) ∉
      rlc_rightUpperUnionSet gamma delta)
    (hend : (delta.1.2.1 : Site 2) ∈
      rlc_rightUpperUnionSet gamma delta) :
    ∃ u v : rect 0 (2 * n) (-n) n,
      s((u : Site 2), (v : Site 2)) ∈ rlc_pathEdges delta.1 ∧
      (u : Site 2) ∉ rlc_rightUpperUnionSet gamma delta ∧
      (v : Site 2) ∈ rlc_rightUpperUnionSet gamma delta ∧
      (u : Site 2) ∈ rlc_pathVertices gamma.1 ∧
      (u : Site 2) ∈ rlc_pathVertices delta.1 := by
  obtain ⟨u, v, he, hu, hv, huDelta, huGamma⟩ :=
    rlc_rightTrace_common_switch_before_unsafe_end delta gamma
      (by simpa [rlc_rightUpperUnionSet, Set.union_comm] using hstart)
      (by simpa [rlc_rightUpperUnionSet, Set.union_comm] using hend)
  exact ⟨u, v, he,
    by simpa [rlc_rightUpperUnionSet, Set.union_comm] using hu,
    by simpa [rlc_rightUpperUnionSet, Set.union_comm] using hv,
    huGamma, huDelta⟩


theorem rlc_rightSafeTrace_reaches_common_before_unsafe_end {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    (hstart : (gamma.1.1 : Site 2) ∉
      rlc_rightUpperUnionSet gamma delta)
    (hend : (gamma.1.2.1 : Site 2) ∈
      rlc_rightUpperUnionSet gamma delta) :
    ∃ u : rect 0 (2 * n) (-n) n,
      (u : Site 2) ∈ rlc_pathVertices gamma.1 ∧
      (u : Site 2) ∈ rlc_pathVertices delta.1 ∧
      (rlc_rightSafeTraceGraph gamma delta).Reachable
        ⟨gamma.1.1, leftSide_subset gamma.1.1.2⟩ u := by
  classical
  let p := gamma.1.2.2.1
  obtain ⟨u, v, q, _huv, huvEdge, hqEdges, hqSafe, hv⟩ :=
    rlc_walk_pred_first_exit_prefix p
      (fun z => (z : Site 2) ∉ rlc_rightUpperUnionSet gamma delta)
      (by simpa [p] using hstart) (by simpa [p] using hend)
  have he : s((u : Site 2), (v : Site 2)) ∈
      rlc_pathEdges gamma.1 := by
    simp only [rlc_pathEdges, Finset.mem_image, List.mem_toFinset]
    exact ⟨s(u, v), huvEdge, rfl⟩
  have hcommon := rlc_rightTrace_switchPoint_of_enter_upperUnion
    gamma delta he (hqSafe u q.end_mem_support) (not_not.mp hv)
  refine ⟨u, hcommon.1, hcommon.2, ⟨q.transfer
    (rlc_rightSafeTraceGraph gamma delta) ?_⟩⟩
  intro e heq
  induction e using Sym2.inductionOn with
  | _ a b =>
      have hab := q.adj_of_mem_edges heq
      have habOrig : s(a, b) ∈ p.edges := hqEdges s(a, b) heq
      have habPath : s((a : Site 2), (b : Site 2)) ∈
          rlc_pathEdges gamma.1 := by
        simp only [rlc_pathEdges, Finset.mem_image, List.mem_toFinset]
        exact ⟨s(a, b), habOrig, rfl⟩
      exact ⟨hab, Finset.mem_union_left _ habPath,
        hqSafe a (q.fst_mem_support_of_mem_edges heq),
        hqSafe b (q.snd_mem_support_of_mem_edges heq)⟩


theorem rlc_rightSafeTrace_reaches_common_from_vertex {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    {z : rect 0 (2 * n) (-n) n}
    (hz : z ∈ gamma.1.2.2.1.support)
    (hzSafe : (z : Site 2) ∉ rlc_rightUpperUnionSet gamma delta)
    (hend : (gamma.1.2.1 : Site 2) ∈
      rlc_rightUpperUnionSet gamma delta) :
    ∃ u : rect 0 (2 * n) (-n) n,
      (u : Site 2) ∈ rlc_pathVertices gamma.1 ∧
      (u : Site 2) ∈ rlc_pathVertices delta.1 ∧
      (rlc_rightSafeTraceGraph gamma delta).Reachable z u := by
  classical
  let p := gamma.1.2.2.1
  let tail := p.dropUntil z hz
  obtain ⟨u, v, q, _huv, huvEdge, hqEdges, hqSafe, hv⟩ :=
    rlc_walk_pred_first_exit_prefix tail
      (fun w => (w : Site 2) ∉ rlc_rightUpperUnionSet gamma delta)
      (by simpa [tail] using hzSafe) (by simpa [tail, p] using hend)
  have huvOrig : s(u, v) ∈ p.edges := by
    exact (p.edges_dropUntil_subset (by simpa [p] using hz)) huvEdge
  have he : s((u : Site 2), (v : Site 2)) ∈
      rlc_pathEdges gamma.1 := by
    simp only [rlc_pathEdges, Finset.mem_image, List.mem_toFinset]
    exact ⟨s(u, v), huvOrig, rfl⟩
  have hcommon := rlc_rightTrace_switchPoint_of_enter_upperUnion
    gamma delta he (hqSafe u q.end_mem_support) (not_not.mp hv)
  refine ⟨u, hcommon.1, hcommon.2, ⟨q.transfer
    (rlc_rightSafeTraceGraph gamma delta) ?_⟩⟩
  intro e heq
  induction e using Sym2.inductionOn with
  | _ a b =>
      have hab := q.adj_of_mem_edges heq
      have habTail : s(a, b) ∈ tail.edges := hqEdges s(a, b) heq
      have habOrig : s(a, b) ∈ p.edges := by
        exact (p.edges_dropUntil_subset (by simpa [p] using hz)) habTail
      have habPath : s((a : Site 2), (b : Site 2)) ∈
          rlc_pathEdges gamma.1 := by
        simp only [rlc_pathEdges, Finset.mem_image, List.mem_toFinset]
        exact ⟨s(a, b), habOrig, rfl⟩
      exact ⟨hab, Finset.mem_union_left _ habPath,
        hqSafe a (q.fst_mem_support_of_mem_edges heq),
        hqSafe b (q.snd_mem_support_of_mem_edges heq)⟩


theorem rlc_safe_vertex_reaches_endpoint_or_common {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    {z : rect 0 (2 * n) (-n) n}
    (hz : z ∈ gamma.1.2.2.1.support)
    (hzSafe : (z : Site 2) ∉ rlc_rightUpperUnionSet gamma delta) :
    (rlc_rightSafeTraceGraph gamma delta).Reachable z
        ⟨gamma.1.2.1, rightSide_subset gamma.1.2.1.2⟩ ∨
      ∃ u : rect 0 (2 * n) (-n) n,
        (u : Site 2) ∈ rlc_pathVertices gamma.1 ∧
        (u : Site 2) ∈ rlc_pathVertices delta.1 ∧
        (rlc_rightSafeTraceGraph gamma delta).Reachable z u := by
  classical
  let p := gamma.1.2.2.1
  let tail := p.dropUntil z hz
  by_cases hall : ∀ q ∈ tail.support,
      (q : Site 2) ∉ rlc_rightUpperUnionSet gamma delta
  · left
    refine ⟨tail.transfer (rlc_rightSafeTraceGraph gamma delta) ?_⟩
    intro e he
    induction e using Sym2.inductionOn with
    | _ a b =>
        have habTail := tail.adj_of_mem_edges he
        have habOrig : s(a, b) ∈ p.edges :=
          p.edges_dropUntil_subset hz he
        have habPath : s((a : Site 2), (b : Site 2)) ∈
            rlc_pathEdges gamma.1 := by
          simp only [rlc_pathEdges, Finset.mem_image, List.mem_toFinset]
          exact ⟨s(a, b), habOrig, rfl⟩
        exact ⟨habTail, Finset.mem_union_left _ habPath,
          hall a (tail.fst_mem_support_of_mem_edges he),
          hall b (tail.snd_mem_support_of_mem_edges he)⟩
  · right
    push Not at hall
    obtain ⟨v0, hv0Supp, hv0Unsafe⟩ := hall
    let initial := tail.takeUntil v0 hv0Supp
    obtain ⟨u, v, q, _huv, huvEdge, hqEdges, hqSafe, hv⟩ :=
      rlc_walk_pred_first_exit_prefix initial
        (fun w => (w : Site 2) ∉ rlc_rightUpperUnionSet gamma delta)
        (by simpa [initial, tail] using hzSafe)
        (by simpa [initial] using hv0Unsafe)
    have huvTail : s(u, v) ∈ tail.edges :=
      tail.edges_takeUntil_subset hv0Supp huvEdge
    have huvOrig : s(u, v) ∈ p.edges :=
      p.edges_dropUntil_subset hz huvTail
    have he : s((u : Site 2), (v : Site 2)) ∈
        rlc_pathEdges gamma.1 := by
      simp only [rlc_pathEdges, Finset.mem_image, List.mem_toFinset]
      exact ⟨s(u, v), huvOrig, rfl⟩
    have hcommon := rlc_rightTrace_switchPoint_of_enter_upperUnion
      gamma delta he (hqSafe u q.end_mem_support) (not_not.mp hv)
    refine ⟨u, hcommon.1, hcommon.2, ⟨q.transfer
      (rlc_rightSafeTraceGraph gamma delta) ?_⟩⟩
    intro e heq
    induction e using Sym2.inductionOn with
    | _ a b =>
        have hab := q.adj_of_mem_edges heq
        have habInitial : s(a, b) ∈ initial.edges := hqEdges s(a, b) heq
        have habTail : s(a, b) ∈ tail.edges :=
          tail.edges_takeUntil_subset hv0Supp habInitial
        have habOrig : s(a, b) ∈ p.edges :=
          p.edges_dropUntil_subset hz habTail
        have habPath : s((a : Site 2), (b : Site 2)) ∈
            rlc_pathEdges gamma.1 := by
          simp only [rlc_pathEdges, Finset.mem_image, List.mem_toFinset]
          exact ⟨s(a, b), habOrig, rfl⟩
        exact ⟨hab, Finset.mem_union_left _ habPath,
          hqSafe a (q.fst_mem_support_of_mem_edges heq),
          hqSafe b (q.snd_mem_support_of_mem_edges heq)⟩


theorem rlc_safe_left_anchor_reaches_common_of_unsafe_ends {n : ℤ}
    (hn : 0 < n) (gamma delta : RlcRightDiagonalPath n)
    (hgammaEnd : (gamma.1.2.1 : Site 2) ∈
      rlc_rightUpperUnionSet gamma delta)
    (hdeltaEnd : (delta.1.2.1 : Site 2) ∈
      rlc_rightUpperUnionSet gamma delta) :
    ∃ (z : leftSide 0 (2 * n) (-n) n)
      (u : rect 0 (2 * n) (-n) n),
      (z : Site 2) ∈ rlc_lowerHalf ∧
      (u : Site 2) ∈ rlc_pathVertices gamma.1 ∧
      (u : Site 2) ∈ rlc_pathVertices delta.1 ∧
      (rlc_rightSafeTraceGraph gamma delta).Reachable
        ⟨z, leftSide_subset z.2⟩ u := by
  classical
  obtain ⟨z, hzHalf, hzUnion, hzSafe⟩ :=
    rlc_exists_safe_left_trace_anchor hn gamma delta
  let zs : rect 0 (2 * n) (-n) n := ⟨z, leftSide_subset z.2⟩
  rcases Finset.mem_union.mp hzUnion with hzGamma | hzDelta
  · simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset] at hzGamma
    obtain ⟨zg, hzg, hzgz⟩ := hzGamma
    have hzgEq : zg = zs := by
      apply Subtype.ext
      exact hzgz
    subst zg
    obtain ⟨u, huGamma, huDelta, hreach⟩ :=
      rlc_rightSafeTrace_reaches_common_from_vertex gamma delta hzg hzSafe hgammaEnd
    exact ⟨z, u, hzHalf, huGamma, huDelta, hreach⟩
  · simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset] at hzDelta
    obtain ⟨zd, hzd, hzdz⟩ := hzDelta
    have hzdEq : zd = zs := by
      apply Subtype.ext
      exact hzdz
    subst zd
    obtain ⟨u, huDelta, huGamma, hreach⟩ :=
      rlc_rightSafeTrace_reaches_common_from_vertex delta gamma hzd
        (by simpa [rlc_rightUpperUnionSet, Set.union_comm] using hzSafe)
        (by simpa [rlc_rightUpperUnionSet, Set.union_comm] using hdeltaEnd)
    refine ⟨z, u, hzHalf, huGamma, huDelta, ?_⟩
    simpa [rlc_rightSafeTraceGraph, rlc_rightUpperUnionSet,
      Finset.union_comm, Set.union_comm] using hreach


theorem rlc_rightSafeTraceGraph_adj_of_pathEdge {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    {u v : rect 0 (2 * n) (-n) n}
    (he : s((u : Site 2), (v : Site 2)) ∈
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges delta.1)
    (hu : (u : Site 2) ∉ rlc_rightUpperUnionSet gamma delta)
    (hv : (v : Site 2) ∉ rlc_rightUpperUnionSet gamma delta) :
    (rlc_rightSafeTraceGraph gamma delta).Adj u v := by
  rw [Finset.mem_union] at he
  rcases he with heGamma | heDelta
  · exact ⟨rlc_pathEdge_lattice gamma.1 heGamma,
      Finset.mem_union_left _ heGamma, hu, hv⟩
  · exact ⟨rlc_pathEdge_lattice delta.1 heDelta,
      Finset.mem_union_right _ heDelta, hu, hv⟩


theorem rlc_rightSafeTraceGraph_reachable_dest_safe {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    {u v : rect 0 (2 * n) (-n) n}
    (hu : (u : Site 2) ∉ rlc_rightUpperUnionSet gamma delta)
    (hreach : (rlc_rightSafeTraceGraph gamma delta).Reachable u v) :
    (v : Site 2) ∉ rlc_rightUpperUnionSet gamma delta := by
  obtain ⟨p⟩ := hreach
  induction p with
  | nil => exact hu
  | @cons a b c hab p ih =>
      exact ih hab.2.2.2


theorem rlc_rightSafeTraceReachable_of_path_safe {n : ℤ}
    (gamma delta eta : RlcRightDiagonalPath n)
    (hedges : rlc_pathEdges eta.1 ⊆
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges delta.1)
    (hsafe : Disjoint (rlc_rightUpperUnionSet gamma delta)
      (rlc_pathVertices eta.1 : Set (Site 2))) :
    ∃ (x : leftSide 0 (2 * n) (-n) n)
      (y : rightSide 0 (2 * n) (-n) n),
      (x : Site 2) ∈ rlc_lowerHalf ∧
      (y : Site 2) ∈ rlc_upperHalf ∧
      (x : Site 2) ∉ rlc_rightUpperUnionSet gamma delta ∧
      (y : Site 2) ∉ rlc_rightUpperUnionSet gamma delta ∧
      (rlc_rightSafeTraceGraph gamma delta).Reachable
        ⟨x, leftSide_subset x.2⟩ ⟨y, rightSide_subset y.2⟩ := by
  classical
  let p := eta.1.2.2.1
  have hpStart : (eta.1.1 : Site 2) ∈ rlc_pathVertices eta.1 := by
    simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
    refine ⟨⟨eta.1.1, leftSide_subset eta.1.1.2⟩, ?_, rfl⟩
    simp
  have hpEnd : (eta.1.2.1 : Site 2) ∈ rlc_pathVertices eta.1 := by
    simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
    refine ⟨⟨eta.1.2.1, rightSide_subset eta.1.2.1.2⟩, ?_, rfl⟩
    simp
  have hstartSafe : (eta.1.1 : Site 2) ∉
      rlc_rightUpperUnionSet gamma delta :=
    fun h => (Set.disjoint_left.mp hsafe) h hpStart
  have hendSafe : (eta.1.2.1 : Site 2) ∉
      rlc_rightUpperUnionSet gamma delta :=
    fun h => (Set.disjoint_left.mp hsafe) h hpEnd
  have hp : (rlc_rightSafeTraceGraph gamma delta).Walk
      ⟨eta.1.1, leftSide_subset eta.1.1.2⟩
      ⟨eta.1.2.1, rightSide_subset eta.1.2.1.2⟩ := by
    apply p.transfer (rlc_rightSafeTraceGraph gamma delta)
    intro e he
    induction e using Sym2.inductionOn with
    | _ u v =>
        have huv : s((u : Site 2), (v : Site 2)) ∈
            rlc_pathEdges eta.1 := by
          simp only [rlc_pathEdges, Finset.mem_image, List.mem_toFinset]
          exact ⟨s(u, v), he, by simp⟩
        have hends := rlc_pathEdge_endpoints_mem_vertices eta.1 huv
        exact ⟨p.adj_of_mem_edges he, hedges huv,
          fun hu => (Set.disjoint_left.mp hsafe) hu hends.1,
          fun hv => (Set.disjoint_left.mp hsafe) hv hends.2⟩
  exact ⟨eta.1.1, eta.1.2.1, eta.2.1, eta.2.2,
    hstartSafe, hendSafe, ⟨hp⟩⟩


theorem rlc_rightSafeTraceReachable_of_left_trace {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    (hcross : Disjoint (rlc_strictTopSet delta)
      (rlc_pathVertices gamma.1 : Set (Site 2))) :
    ∃ (x : leftSide 0 (2 * n) (-n) n)
      (y : rightSide 0 (2 * n) (-n) n),
      (x : Site 2) ∈ rlc_lowerHalf ∧
      (y : Site 2) ∈ rlc_upperHalf ∧
      (x : Site 2) ∉ rlc_rightUpperUnionSet gamma delta ∧
      (y : Site 2) ∉ rlc_rightUpperUnionSet gamma delta ∧
      (rlc_rightSafeTraceGraph gamma delta).Reachable
        ⟨x, leftSide_subset x.2⟩ ⟨y, rightSide_subset y.2⟩ := by
  apply rlc_rightSafeTraceReachable_of_path_safe gamma delta gamma
  · intro e he
    exact Finset.mem_union_left _ he
  · rw [rlc_rightUpperUnionSet, Set.disjoint_union_left]
    exact ⟨rlc_strictTopSet_disjoint_path gamma, hcross⟩


theorem rlc_rightSafeTraceReachable_of_right_trace {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    (hcross : Disjoint (rlc_strictTopSet gamma)
      (rlc_pathVertices delta.1 : Set (Site 2))) :
    ∃ (x : leftSide 0 (2 * n) (-n) n)
      (y : rightSide 0 (2 * n) (-n) n),
      (x : Site 2) ∈ rlc_lowerHalf ∧
      (y : Site 2) ∈ rlc_upperHalf ∧
      (x : Site 2) ∉ rlc_rightUpperUnionSet gamma delta ∧
      (y : Site 2) ∉ rlc_rightUpperUnionSet gamma delta ∧
      (rlc_rightSafeTraceGraph gamma delta).Reachable
        ⟨x, leftSide_subset x.2⟩ ⟨y, rightSide_subset y.2⟩ := by
  apply rlc_rightSafeTraceReachable_of_path_safe gamma delta delta
  · intro e he
    exact Finset.mem_union_right _ he
  · rw [rlc_rightUpperUnionSet, Set.disjoint_union_left]
    exact ⟨hcross, rlc_strictTopSet_disjoint_path delta⟩


theorem rlc_rightSafeTraceReachable_self {n : ℤ}
    (gamma : RlcRightDiagonalPath n) :
    ∃ (x : leftSide 0 (2 * n) (-n) n)
      (y : rightSide 0 (2 * n) (-n) n),
      (x : Site 2) ∈ rlc_lowerHalf ∧
      (y : Site 2) ∈ rlc_upperHalf ∧
      (x : Site 2) ∉ rlc_rightUpperUnionSet gamma gamma ∧
      (y : Site 2) ∉ rlc_rightUpperUnionSet gamma gamma ∧
      (rlc_rightSafeTraceGraph gamma gamma).Reachable
        ⟨x, leftSide_subset x.2⟩ ⟨y, rightSide_subset y.2⟩ :=
  rlc_rightSafeTraceReachable_of_left_trace gamma gamma
    (rlc_strictTopSet_disjoint_path gamma)


theorem rlc_rightSafeTraceReachable_of_disjoint_start_left {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    (hdisj : Disjoint (rlc_pathVertices delta.1)
      (rlc_pathVertices gamma.1))
    (hstart : (gamma.1.1 : Site 2) ∉ rlc_strictTopSet delta) :
    ∃ (x : leftSide 0 (2 * n) (-n) n)
      (y : rightSide 0 (2 * n) (-n) n),
      (x : Site 2) ∈ rlc_lowerHalf ∧
      (y : Site 2) ∈ rlc_upperHalf ∧
      (x : Site 2) ∉ rlc_rightUpperUnionSet gamma delta ∧
      (y : Site 2) ∉ rlc_rightUpperUnionSet gamma delta ∧
      (rlc_rightSafeTraceGraph gamma delta).Reachable
        ⟨x, leftSide_subset x.2⟩ ⟨y, rightSide_subset y.2⟩ := by
  apply rlc_rightSafeTraceReachable_of_left_trace gamma delta
  rw [Set.disjoint_left]
  intro z hzTop hzGamma
  have hiff := rlc_strictTopSet_mem_iff_path_start_of_disjoint
    delta gamma hdisj hzGamma
  exact hstart (hiff.mp hzTop)


theorem rlc_rightSafeTraceReachable_of_disjoint_start_right {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    (hdisj : Disjoint (rlc_pathVertices gamma.1)
      (rlc_pathVertices delta.1))
    (hstart : (delta.1.1 : Site 2) ∉ rlc_strictTopSet gamma) :
    ∃ (x : leftSide 0 (2 * n) (-n) n)
      (y : rightSide 0 (2 * n) (-n) n),
      (x : Site 2) ∈ rlc_lowerHalf ∧
      (y : Site 2) ∈ rlc_upperHalf ∧
      (x : Site 2) ∉ rlc_rightUpperUnionSet gamma delta ∧
      (y : Site 2) ∉ rlc_rightUpperUnionSet gamma delta ∧
      (rlc_rightSafeTraceGraph gamma delta).Reachable
        ⟨x, leftSide_subset x.2⟩ ⟨y, rightSide_subset y.2⟩ := by
  apply rlc_rightSafeTraceReachable_of_right_trace gamma delta
  rw [Set.disjoint_left]
  intro z hzTop hzDelta
  have hiff := rlc_strictTopSet_mem_iff_path_start_of_disjoint
    gamma delta hdisj hzDelta
  exact hstart (hiff.mp hzTop)


theorem rlc_rightSafeTraceReachable_of_disjoint {n : ℤ} (hn : 0 < n)
    (gamma delta : RlcRightDiagonalPath n)
    (hdisj : Disjoint (rlc_pathVertices gamma.1)
      (rlc_pathVertices delta.1)) :
    ∃ (x : leftSide 0 (2 * n) (-n) n)
      (y : rightSide 0 (2 * n) (-n) n),
      (x : Site 2) ∈ rlc_lowerHalf ∧
      (y : Site 2) ∈ rlc_upperHalf ∧
      (x : Site 2) ∉ rlc_rightUpperUnionSet gamma delta ∧
      (y : Site 2) ∉ rlc_rightUpperUnionSet gamma delta ∧
      (rlc_rightSafeTraceGraph gamma delta).Reachable
        ⟨x, leftSide_subset x.2⟩ ⟨y, rightSide_subset y.2⟩ := by
  by_cases hgammaStart :
      (gamma.1.1 : Site 2) ∈ rlc_strictTopSet delta
  · have hgammaTop : (rlc_pathVertices gamma.1 : Set (Site 2)) ⊆
        rlc_strictTopSet delta := by
      intro z hz
      exact (rlc_strictTopSet_mem_iff_path_start_of_disjoint
        delta gamma hdisj.symm hz).mpr hgammaStart
    have hdeltaStart :
        (delta.1.1 : Site 2) ∉ rlc_strictTopSet gamma := by
      intro hdeltaStart
      have hdeltaTop : (rlc_pathVertices delta.1 : Set (Site 2)) ⊆
          rlc_strictTopSet gamma := by
        intro z hz
        exact (rlc_strictTopSet_mem_iff_path_start_of_disjoint
          gamma delta hdisj hz).mpr hdeltaStart
      exact rlc_disjointRightPaths_not_mutually_top
        hn gamma delta hdisj ⟨hgammaTop, hdeltaTop⟩
    exact rlc_rightSafeTraceReachable_of_disjoint_start_right
      gamma delta hdisj hdeltaStart
  · exact rlc_rightSafeTraceReachable_of_disjoint_start_left
      gamma delta hdisj.symm hgammaStart


end Universality
end StatMech
