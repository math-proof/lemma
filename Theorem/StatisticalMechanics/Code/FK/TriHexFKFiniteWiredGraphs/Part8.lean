/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredGraphs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredSweep.Part3
import Theorem.StatisticalMechanics.Code.FK.TriHexFKTorusSweep.Part15
import Def.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredGraphs.Part9
open Finset Set


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open Universality

noncomputable section

theorem triHexPlanarFiniteTriangle_openSub_adj_sector
    (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteTriangleGraph n).edgeSet)
    {x y : TriHexPlanarFiniteTerminal n}
    (hxy : (openSub (triHexPlanarFiniteTriangleGraph n)
      (extendActive (triHexPlanarFiniteTriangleGraph n) omega)).Adj x y) :
    (triHexPlanarFiniteTriangleSectorGraph n omega).Adj x y := by
  have hmem : s(x, y) ∈ (triHexPlanarFiniteTriangleGraph n).edgeSet := by
    rw [SimpleGraph.mem_edgeSet]
    exact hxy.1
  let e : (triHexPlanarFiniteTriangleGraph n).edgeSet := ⟨s(x, y), hmem⟩
  let a := (triHexPlanarFiniteTriangleEdgeEquiv n).symm e
  let z := a.1
  let i := a.2
  have ha : triHexPlanarFiniteTriangleEdgeEquiv n (z, i) = e := by
    simpa [z, i, a] using
      (triHexPlanarFiniteTriangleEdgeEquiv n).apply_symm_apply e
  have hedge : s(x, y) =
      s(triHexPlanarFiniteTerminalMap n z (triHexTriangleEdgeTerminal1 i),
        triHexPlanarFiniteTerminalMap n z
          (triHexTriangleEdgeTerminal2 i)) := by
    calc
      s(x, y) = e.1 := rfl
      _ = (triHexPlanarFiniteTriangleEdgeEquiv n (z, i)).1 :=
        congrArg Subtype.val ha.symm
      _ = _ := rfl
  have hopen : omega e = true := by
    have := hxy.2
    simpa [extendActive, e, hmem] using this
  have hlocal : triHexLocalDirection
      (triHexPlanarFiniteTriangleConfigEquiv n omega z) i = true := by
    rw [triHexPlanarFiniteTriangleConfigEquiv_direction]
    rw [ha]
    exact hopen
  have hconnects := triangleFKLocalConnectivity_connects_of_direction
    (triHexPlanarFiniteTriangleConfigEquiv n omega z) i hlocal
  rw [triHexPlanarFiniteTriangleSectorGraph, triHexFKTerminalSectorGraph,
    SimpleGraph.fromEdgeSet_adj]
  exact ⟨⟨z, triHexTriangleEdgeTerminal1 i,
    triHexTriangleEdgeTerminal2 i, hconnects, hedge⟩, hxy.ne⟩


theorem triHexPlanarFiniteTriangle_sector_adj_openSub_reachable
    (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteTriangleGraph n).edgeSet)
    {x y : TriHexPlanarFiniteTerminal n}
    (hxy : (triHexPlanarFiniteTriangleSectorGraph n omega).Adj x y) :
    (openSub (triHexPlanarFiniteTriangleGraph n)
      (extendActive (triHexPlanarFiniteTriangleGraph n) omega)).Reachable x y := by
  rw [triHexPlanarFiniteTriangleSectorGraph, triHexFKTerminalSectorGraph,
    SimpleGraph.fromEdgeSet_adj] at hxy
  obtain ⟨⟨z, i, j, hconnects, hedge⟩, _⟩ := hxy
  have hreach := triHexPlanarFiniteTriangle_openSub_reachable_of_connects
    n omega z i j hconnects
  rw [Sym2.eq_iff] at hedge
  rcases hedge with ⟨hxi, hyj⟩ | ⟨hxj, hyi⟩
  · simpa [hxi, hyj] using hreach
  · simpa [hxj, hyi] using hreach.symm


theorem triHexPlanarFiniteTriangle_openSub_reachable_iff_sector
    (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteTriangleGraph n).edgeSet)
    (x y : TriHexPlanarFiniteTerminal n) :
    (openSub (triHexPlanarFiniteTriangleGraph n)
      (extendActive (triHexPlanarFiniteTriangleGraph n) omega)).Reachable x y ↔
      (triHexPlanarFiniteTriangleSectorGraph n omega).Reachable x y := by
  constructor
  · exact fun h => reachable_map_of_adj_reachable _ _ id
      (fun _ _ hab => SimpleGraph.Adj.reachable
        (triHexPlanarFiniteTriangle_openSub_adj_sector n omega hab)) h
  · exact fun h => reachable_map_of_adj_reachable _ _ id
      (fun _ _ hab =>
        triHexPlanarFiniteTriangle_sector_adj_openSub_reachable n omega hab) h


end
end StatMech.FK.PeriodicPlanar
