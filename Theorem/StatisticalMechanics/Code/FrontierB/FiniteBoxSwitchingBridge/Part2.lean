/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteBoxSwitchingBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.PairSourceBoxCurrent.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentConnectivityDiagonal.Part2
import Def.StatisticalMechanics.Code.FrontierB.FiniteBoxSwitchingBridge.Part2
open MeasureTheory Set SimpleGraph
open scoped ENNReal symmDiff


namespace StatMech.FrontierB

open Sharpness Lattice Percolation


theorem finiteBoxCurrentTrace_ofEdgeFun_add
    (d n : ℕ)
    (m q : EdgeCurrent (StatMech.FK.boxGraph d n)) :
    finiteBoxCurrentTrace d n
        (ofEdgeFun (StatMech.FK.boxGraph d n) (fun e => m e + q e)) =
      superposedCurrentTrace
        (extendBoxCurrent d n m, extendBoxCurrent d n q) := by
  ext e
  by_cases he : e ∈ Set.range (boxCurrentEdgeIncl d n)
  · obtain ⟨eb, rfl⟩ := he
    simp [finiteBoxCurrentTrace, currentTrace, superposedCurrentTrace,
      edgeCurrentOfCurrent, ofEdgeFun, extendBoxCurrent_included]
  · simp [finiteBoxCurrentTrace, currentTrace, superposedCurrentTrace,
      edgeCurrentOfCurrent, ofEdgeFun,
      extendBoxCurrent_outside d n _ e he]


theorem currentSubgraph_ofEdgeFun_add_eq_openSubgraphInduce
    (d n : ℕ)
    (m q : EdgeCurrent (StatMech.FK.boxGraph d n)) :
    currentSubgraph (StatMech.FK.boxGraph d n)
        (ofEdgeFun (StatMech.FK.boxGraph d n) (fun e => m e + q e)) =
      openSubgraphInduce d
        (superposedCurrentTrace
          (extendBoxCurrent d n m, extendBoxCurrent d n q))
        (box d n) := by
  ext a b
  let G := StatMech.FK.boxGraph d n
  constructor
  · rintro ⟨hab, hpos⟩
    have he : s(a, b) ∈ G.edgeFinset :=
      SimpleGraph.mem_edgeFinset.mpr hab
    have hcoord : boxCurrentEdgeIncl d n ⟨s(a, b), he⟩ =
        s((a : Site d), (b : Site d)) := by
      rfl
    refine ⟨hab, ?_⟩
    change superposedCurrentTrace
      (extendBoxCurrent d n m, extendBoxCurrent d n q)
        s((a : Site d), (b : Site d)) = true
    rw [← hcoord, superposedCurrentTrace_apply]
    change 0 < extendBoxCurrent d n m
        (boxCurrentEdgeIncl d n ⟨s(a, b), he⟩) +
      extendBoxCurrent d n q (boxCurrentEdgeIncl d n ⟨s(a, b), he⟩)
    rw [extendBoxCurrent_included, extendBoxCurrent_included]
    rw [ofEdgeFun, dif_pos he] at hpos
    omega
  · rintro ⟨hab, hopen⟩
    have he : s(a, b) ∈ G.edgeFinset :=
      SimpleGraph.mem_edgeFinset.mpr hab
    have hcoord : boxCurrentEdgeIncl d n ⟨s(a, b), he⟩ =
        s((a : Site d), (b : Site d)) := by
      rfl
    refine ⟨hab, ?_⟩
    change superposedCurrentTrace
      (extendBoxCurrent d n m, extendBoxCurrent d n q)
        s((a : Site d), (b : Site d)) = true at hopen
    rw [← hcoord, superposedCurrentTrace_apply] at hopen
    change 0 < extendBoxCurrent d n m
        (boxCurrentEdgeIncl d n ⟨s(a, b), he⟩) +
      extendBoxCurrent d n q (boxCurrentEdgeIncl d n ⟨s(a, b), he⟩) at hopen
    rw [extendBoxCurrent_included, extendBoxCurrent_included] at hopen
    rw [ofEdgeFun, dif_pos he]
    omega


theorem currentConnected_ofEdgeFun_add_iff_boxConnectionEvent
    (d n : ℕ)
    (m q : EdgeCurrent (StatMech.FK.boxGraph d n))
    (x y : StatMech.FK.boxVerts d n) :
    CurrentConnected (StatMech.FK.boxGraph d n)
        (ofEdgeFun (StatMech.FK.boxGraph d n) (fun e => m e + q e)) x y ↔
      superposedCurrentTrace
          (extendBoxCurrent d n m, extendBoxCurrent d n q) ∈
        boxConnectionEvent n (x : Site d) (y : Site d) := by
  rw [CurrentConnected, currentSubgraph_ofEdgeFun_add_eq_openSubgraphInduce]
  constructor
  · intro h
    exact ⟨x.2, y.2, h⟩
  · rintro ⟨hx, hy, h⟩
    simpa only [Subsingleton.elim hx x.2, Subsingleton.elim hy y.2] using h


end StatMech.FrontierB
