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
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part9
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_iUnion_pathOpen (a b c d : ℤ) :
    (⋃ gamma : RlcCrossingPath a b c d, rlc_pathOpen gamma) =
      horizontalCrossingEvent a b c d := by
  ext omega
  constructor
  · intro h
    simp only [Set.mem_iUnion] at h
    obtain ⟨gamma, hgamma⟩ := h
    refine ⟨gamma.1, gamma.2.1, ⟨rlc_openWalkOfEdges omega gamma.2.2.1 ?_⟩⟩
    change ∀ e ∈ gamma.2.2.1.edges.toFinset.image (Sym2.map Subtype.val),
      omega e = true at hgamma
    exact hgamma
  · rintro ⟨x, y, hxy⟩
    let q0 := hxy.some
    have hle : openSubgraphInduce 2 omega (rect a b c d) ≤
        (hypercubicLattice 2).induce (rect a b c d) := by
      intro u v huv
      rw [openSubgraphInduce_adj, openSubgraph_adj] at huv
      exact huv.1
    let q := q0.mapLe hle
    let gamma : RlcCrossingPath a b c d := ⟨x, y, q.toPath⟩
    simp only [Set.mem_iUnion]
    refine ⟨gamma, ?_⟩
    intro e he
    simp only [rlc_pathEdges, Finset.mem_image, List.mem_toFinset] at he
    obtain ⟨z, hz, rfl⟩ := he
    have hzq : z ∈ q.edges := q.edges_toPath_subset hz
    have hedge : q.edges = q0.edges := rlc_edges_mapLe_eq hle q0
    have hzq0 : z ∈ q0.edges := hedge ▸ hzq
    induction z using Sym2.inductionOn with
    | _ u v =>
      have hadj := q0.adj_of_mem_edges hzq0
      rw [openSubgraphInduce_adj, openSubgraph_adj] at hadj
      simpa using hadj.2


theorem rlc_iUnion_betweenPathOpen {a b c d : ℤ}
    (P Q : Finset (rect a b c d)) :
    (⋃ gamma : RlcBetweenPath P Q, rlc_betweenPathOpen gamma) =
      rlc_betweenEvent P Q := by
  ext omega
  constructor
  · intro h
    simp only [Set.mem_iUnion] at h
    obtain ⟨gamma, hgamma⟩ := h
    refine ⟨gamma.1, gamma.2.1, ⟨rlc_openWalkOfEdges omega gamma.2.2.1 ?_⟩⟩
    change ∀ e ∈ gamma.2.2.1.edges.toFinset.image (Sym2.map Subtype.val),
      omega e = true at hgamma
    exact hgamma
  · rintro ⟨x, y, hxy⟩
    let q0 := hxy.some
    have hle : openSubgraphInduce 2 omega (rect a b c d) ≤
        (hypercubicLattice 2).induce (rect a b c d) := by
      intro u v huv
      rw [openSubgraphInduce_adj, openSubgraph_adj] at huv
      exact huv.1
    let q := q0.mapLe hle
    let gamma : RlcBetweenPath P Q := ⟨x, y, q.toPath⟩
    simp only [Set.mem_iUnion]
    refine ⟨gamma, ?_⟩
    intro e he
    simp only [rlc_betweenPathEdges, Finset.mem_image, List.mem_toFinset] at he
    obtain ⟨z, hz, rfl⟩ := he
    have hzq : z ∈ q.edges := q.edges_toPath_subset hz
    have hedge : q.edges = q0.edges := rlc_edges_mapLe_eq hle q0
    have hzq0 : z ∈ q0.edges := hedge ▸ hzq
    induction z using Sym2.inductionOn with
    | _ u v =>
      have hadj := q0.adj_of_mem_edges hzq0
      rw [openSubgraphInduce_adj, openSubgraph_adj] at hadj
      simpa using hadj.2

theorem rlc_horizontalCrossingEvent_measurableSet (a b c d : ℤ) :
    MeasurableSet (horizontalCrossingEvent a b c d) := by
  rw [← rlc_iUnion_pathOpen]
  exact MeasurableSet.iUnion fun gamma => rlc_pathOpen_measurableSet gamma


theorem rlc_verticalCrossingEvent_dependsOn (a b c d : ℤ) :
    DependsOn ((verticalCrossingEvent a b c d).indicator (fun _ => (1 : ℝ)))
      (edgesWithinFinset (rect_finite a b c d).toFinset : Set (Sym2 (Site 2))) := by
  let S := (rect_finite a b c d).toFinset
  have hSco : (S : Set (Site 2)) = rect a b c d := by
    ext z
    simp [S]
  intro omega omega' hagree
  have hconn : ∀ (x y : Site 2),
      (∃ (hx : x ∈ rect a b c d) (hy : y ∈ rect a b c d),
        ConnectedWithin 2 omega (rect a b c d) ⟨x, hx⟩ ⟨y, hy⟩) ↔
      (∃ (hx : x ∈ rect a b c d) (hy : y ∈ rect a b c d),
        ConnectedWithin 2 omega' (rect a b c d) ⟨x, hx⟩ ⟨y, hy⟩) := by
    intro x y
    rw [← hSco]
    exact withinConn_congr S x y hagree
  have hevent : omega ∈ verticalCrossingEvent a b c d ↔
      omega' ∈ verticalCrossingEvent a b c d := by
    constructor
    · rintro ⟨x, y, hxy⟩
      have hc : ∃ (hx' : (x : Site 2) ∈ rect a b c d)
          (hy' : (y : Site 2) ∈ rect a b c d),
          ConnectedWithin 2 omega (rect a b c d) ⟨x, hx'⟩ ⟨y, hy'⟩ :=
        ⟨bottomSide_subset x.2, topSide_subset y.2, hxy⟩
      obtain ⟨_, _, hc'⟩ := (hconn x y).mp hc
      exact ⟨x, y, hc'⟩
    · rintro ⟨x, y, hxy⟩
      have hc : ∃ (hx' : (x : Site 2) ∈ rect a b c d)
          (hy' : (y : Site 2) ∈ rect a b c d),
          ConnectedWithin 2 omega' (rect a b c d) ⟨x, hx'⟩ ⟨y, hy'⟩ :=
        ⟨bottomSide_subset x.2, topSide_subset y.2, hxy⟩
      obtain ⟨_, _, hc'⟩ := (hconn x y).mpr hc
      exact ⟨x, y, hc'⟩
  by_cases hmem : omega ∈ verticalCrossingEvent a b c d
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hevent.mp hmem)]
  · rw [Set.indicator_of_notMem hmem,
      Set.indicator_of_notMem (fun h => hmem (hevent.mpr h))]

theorem rlc_verticalCrossingEvent_measurableSet (a b c d : ℤ) :
    MeasurableSet (verticalCrossingEvent a b c d) :=
  measurableSet_of_dependsOn (rlc_verticalCrossingEvent_dependsOn a b c d)


end Universality
end StatMech
