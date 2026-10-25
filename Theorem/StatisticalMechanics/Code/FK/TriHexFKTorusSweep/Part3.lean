/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKGlobalSweep.Part5
import Theorem.StatisticalMechanics.Code.FK.TriHexTorusDuality.Part10
import Theorem.StatisticalMechanics.Code.FK.ActiveEdges.Part4
import Theorem.StatisticalMechanics.Code.Universality.STTTransport.Part3
import Def.StatisticalMechanics.Code.FK.TriHexFKTorusSweep.Part3


namespace StatMech.FK.PeriodicPlanar

open Universality

open scoped BigOperators


theorem triangularTorus_openSub_adj_terminalSectorGraph
    (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (triangularTorusGraph L).edgeSet)
    {x y : TorusSite L}
    (hxy : (openSub (triangularTorusGraph L)
      (extendActive (triangularTorusGraph L) omega)).Adj x y) :
    (triangularTorusTerminalSectorGraph L omega).Adj x y := by
  have hmem : s(x, y) ∈ (triangularTorusGraph L).edgeSet := by
    rw [SimpleGraph.mem_edgeSet]
    exact hxy.1
  let e : (triangularTorusGraph L).edgeSet := ⟨s(x, y), hmem⟩
  let a := (triHexTorusTriangleSweepEdgeEquiv L).symm e
  let z := a.1
  let i := a.2
  have ha : triHexTorusTriangleSweepEdgeEquiv L (z, i) = e := by
    simpa [z, i, a] using
      (triHexTorusTriangleSweepEdgeEquiv L).apply_symm_apply e
  have hedge : s(x, y) =
      s(triHexTorusCellTerminal L z (triHexTriangleEdgeTerminal1 i),
        triHexTorusCellTerminal L z (triHexTriangleEdgeTerminal2 i)) := by
    calc
      s(x, y) = e.1 := rfl
      _ = (triHexTorusTriangleSweepEdgeEquiv L (z, i)).1 :=
        congrArg Subtype.val ha.symm
      _ = _ := triHexTorusTriangleSweepEdge_val L z i
  have hopen : omega e = true := by
    have := hxy.2
    simpa [extendActive, e, hmem] using this
  have hlocal : triHexLocalDirection
      (triangularTorusActiveConfigEquiv L omega z) i = true := by
    have hopen' : omega (triHexTorusTriangleSweepEdgeEquiv L (z, i)) = true := by
      rw [ha]
      exact hopen
    rw [triangularTorusActiveConfigEquiv_direction]
    exact hopen'
  have hconnects := triangleFKLocalConnectivity_connects_of_direction
    (triangularTorusActiveConfigEquiv L omega z) i hlocal
  rw [triangularTorusTerminalSectorGraph, triHexFKTerminalSectorGraph,
    SimpleGraph.fromEdgeSet_adj]
  exact ⟨⟨z, triHexTriangleEdgeTerminal1 i, triHexTriangleEdgeTerminal2 i,
    hconnects, hedge⟩, hxy.ne⟩


theorem triangularTorus_terminalSectorGraph_adj_openSub_reachable
    (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (triangularTorusGraph L).edgeSet)
    {x y : TorusSite L}
    (hxy : (triangularTorusTerminalSectorGraph L omega).Adj x y) :
    (openSub (triangularTorusGraph L)
      (extendActive (triangularTorusGraph L) omega)).Reachable x y := by
  rw [triangularTorusTerminalSectorGraph, triHexFKTerminalSectorGraph,
    SimpleGraph.fromEdgeSet_adj] at hxy
  obtain ⟨⟨z, i, j, hconnects, hedge⟩, _hxyne⟩ := hxy
  have hreach := triangularTorus_openSub_reachable_of_connects
    L omega z i j hconnects
  rw [Sym2.eq_iff] at hedge
  rcases hedge with ⟨hxi, hyj⟩ | ⟨hxj, hyi⟩
  · simpa [hxi, hyj] using hreach
  · simpa [hxj, hyi] using hreach.symm


theorem triangularTorus_openSub_reachable_iff_terminalSectorGraph
    (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (triangularTorusGraph L).edgeSet)
    (x y : TorusSite L) :
    (openSub (triangularTorusGraph L)
      (extendActive (triangularTorusGraph L) omega)).Reachable x y ↔
      (triangularTorusTerminalSectorGraph L omega).Reachable x y := by
  constructor
  · exact fun h => Universality.reach_collapse _ _ id
      (fun a b hab => SimpleGraph.Adj.reachable
        (triangularTorus_openSub_adj_terminalSectorGraph L omega hab))
      rfl rfl h
  · exact fun h => Universality.reach_collapse _ _ id
      (fun _a _b hab =>
        triangularTorus_terminalSectorGraph_adj_openSub_reachable L omega hab)
      rfl rfl h


end StatMech.FK.PeriodicPlanar
