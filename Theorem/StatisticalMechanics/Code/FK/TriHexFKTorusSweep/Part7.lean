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
import Def.StatisticalMechanics.Code.FK.TriHexFKTorusSweep.Part7


namespace StatMech.FK.PeriodicPlanar

open Universality

open scoped BigOperators


theorem hexagonalTorus_openSub_adj_representative_reachable
    (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (hexagonalTorusGraph L).edgeSet)
    {u v : HexTorusVertex L}
    (huv : (openSub (hexagonalTorusGraph L)
      (extendActive (hexagonalTorusGraph L) omega)).Adj u v) :
    (hexagonalTorusTerminalSectorGraph L omega).Reachable
      (hexagonalTorusOpenRepresentative L omega u)
      (hexagonalTorusOpenRepresentative L omega v) := by
  obtain ⟨⟨z, i⟩, hedge⟩ := huv.1
  rw [hexagonalTorusIndexedEdge, Sym2.eq_iff] at hedge
  have hopen : triHexLocalDirection
      (hexagonalTorusActiveConfigEquiv L omega z) i = true := by
    rw [hexagonalTorusActiveConfigEquiv_direction]
    let e := triHexTorusStarSweepEdgeEquiv L (z, i)
    have heq : (e.1 : Sym2 (HexTorusVertex L)) = s(u, v) := by
      rw [triHexTorusStarSweepEdge_val]
      exact (Sym2.eq_iff).2 hedge
    have := huv.2
    rw [← heq, extendActive_apply] at this
    exact this
  have hselected := starFKRepresentativeDirection_open_of_open
    (hexagonalTorusActiveConfigEquiv L omega z) i hopen
  have hconnects : (starFKLocalConnectivity
      (hexagonalTorusActiveConfigEquiv L omega z)).Connects
        (starFKRepresentativeDirection
          (hexagonalTorusActiveConfigEquiv L omega z)) i :=
    (starFKLocalConnectivity_connects_iff _ _ _).2
      (Or.inr ⟨hselected, hopen⟩)
  have hreach := triHexFKTerminalSectorGraph_reachable_of_connects
    (triHexTorusCellTerminal L)
    (fun z => starFKLocalConnectivity
      (hexagonalTorusActiveConfigEquiv L omega z)) z _ _ hconnects
  rcases hedge with ⟨hu, hv⟩ | ⟨hv, hu⟩
  · subst u
    subst v
    simpa [hexagonalTorusOpenRepresentative,
      hexagonalTorusTerminalSectorGraph] using hreach
  · subst u
    subst v
    simpa [hexagonalTorusOpenRepresentative,
      hexagonalTorusTerminalSectorGraph] using hreach.symm


theorem hexagonalTorus_terminalSectorGraph_adj_openSub_reachable
    (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (hexagonalTorusGraph L).edgeSet)
    {x y : TorusSite L}
    (hxy : (hexagonalTorusTerminalSectorGraph L omega).Adj x y) :
    (openSub (hexagonalTorusGraph L)
      (extendActive (hexagonalTorusGraph L) omega)).Reachable
        (x, true) (y, true) := by
  rw [hexagonalTorusTerminalSectorGraph, triHexFKTerminalSectorGraph,
    SimpleGraph.fromEdgeSet_adj] at hxy
  obtain ⟨⟨z, i, j, hconnects, hedge⟩, _hxyne⟩ := hxy
  have hreach := hexagonalTorus_openSub_reachable_of_connects
    L omega z i j hconnects
  rw [Sym2.eq_iff] at hedge
  rcases hedge with ⟨hxi, hyj⟩ | ⟨hxj, hyi⟩
  · simpa [hxi, hyj] using hreach
  · simpa [hxj, hyi] using hreach.symm


theorem hexagonalTorus_openSub_white_reachable_iff_terminalSectorGraph
    (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (hexagonalTorusGraph L).edgeSet)
    (x y : TorusSite L) :
    (openSub (hexagonalTorusGraph L)
      (extendActive (hexagonalTorusGraph L) omega)).Reachable (x, true) (y, true) ↔
      (hexagonalTorusTerminalSectorGraph L omega).Reachable x y := by
  constructor
  · intro h
    have hc := reachable_map_of_adj_reachable
      (openSub (hexagonalTorusGraph L)
        (extendActive (hexagonalTorusGraph L) omega))
      (hexagonalTorusTerminalSectorGraph L omega)
      (hexagonalTorusOpenRepresentative L omega)
      (fun _ _ hab =>
        hexagonalTorus_openSub_adj_representative_reachable L omega hab)
      h
    simpa [hexagonalTorusOpenRepresentative] using hc
  · intro h
    exact reachable_map_of_adj_reachable
      (hexagonalTorusTerminalSectorGraph L omega)
      (openSub (hexagonalTorusGraph L)
        (extendActive (hexagonalTorusGraph L) omega))
      (fun z => (z, true))
      (fun _ _ hab =>
        hexagonalTorus_terminalSectorGraph_adj_openSub_reachable L omega hab)
      h


theorem hexagonalTorus_openSub_adj_eq_spoke
    (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (hexagonalTorusGraph L).edgeSet)
    {u v : HexTorusVertex L}
    (huv : (openSub (hexagonalTorusGraph L)
      (extendActive (hexagonalTorusGraph L) omega)).Adj u v) :
    ∃ z i, triHexLocalDirection
        (hexagonalTorusActiveConfigEquiv L omega z) i = true ∧
      ((u = (z, false) ∧ v = (triHexTorusCellTerminal L z i, true)) ∨
        (v = (z, false) ∧ u = (triHexTorusCellTerminal L z i, true))) := by
  obtain ⟨⟨z, i⟩, hedge⟩ := huv.1
  rw [hexagonalTorusIndexedEdge, Sym2.eq_iff] at hedge
  have hopen : triHexLocalDirection
      (hexagonalTorusActiveConfigEquiv L omega z) i = true := by
    rw [hexagonalTorusActiveConfigEquiv_direction]
    let e := triHexTorusStarSweepEdgeEquiv L (z, i)
    have heq : (e.1 : Sym2 (HexTorusVertex L)) = s(u, v) := by
      rw [triHexTorusStarSweepEdge_val]
      exact (Sym2.eq_iff).2 hedge
    have := huv.2
    rw [← heq, extendActive_apply] at this
    exact this
  refine ⟨z, i, hopen, ?_⟩
  rcases hedge with ⟨hu, hv⟩ | ⟨hv, hu⟩
  · exact Or.inl ⟨hu.symm, by
      simpa [triHexTorusCellTerminal] using hv.symm⟩
  · exact Or.inr ⟨hv.symm, by
      simpa [triHexTorusCellTerminal] using hu.symm⟩


end StatMech.FK.PeriodicPlanar
