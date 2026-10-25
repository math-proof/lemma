/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredGraphs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredSweep.Part3
import Theorem.StatisticalMechanics.Code.FK.TriHexFKTorusSweep.Part15
import Def.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredGraphs.Part12
open Finset Set


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open Universality

noncomputable section

theorem triHexPlanarFiniteStar_openSub_adj_representative_reachable
    (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet)
    {u v : TriHexPlanarFiniteStarVertex n}
    (huv : (openSub (triHexPlanarFiniteStarGraph n)
      (extendActive (triHexPlanarFiniteStarGraph n) omega)).Adj u v) :
    (triHexPlanarFiniteStarSectorGraph n omega).Reachable
      (triHexPlanarFiniteStarRepresentative n omega u)
      (triHexPlanarFiniteStarRepresentative n omega v) := by
  have hmem : s(u, v) ∈ (triHexPlanarFiniteStarGraph n).edgeSet := by
    rw [SimpleGraph.mem_edgeSet]
    exact huv.1
  let e : (triHexPlanarFiniteStarGraph n).edgeSet := ⟨s(u, v), hmem⟩
  let a := (triHexPlanarFiniteStarEdgeEquiv n).symm e
  let z := a.1
  let i := a.2
  have ha : triHexPlanarFiniteStarEdgeEquiv n (z, i) = e := by
    simpa [z, i, a] using
      (triHexPlanarFiniteStarEdgeEquiv n).apply_symm_apply e
  have hedge : s(Sum.inl z,
      Sum.inr (triHexPlanarFiniteTerminalMap n z i)) = s(u, v) := by
    calc
      _ = (triHexPlanarFiniteStarEdgeEquiv n (z, i)).1 := rfl
      _ = e.1 := congrArg Subtype.val ha
      _ = _ := rfl
  have hopen : triHexLocalDirection
      (triHexPlanarFiniteStarConfigEquiv n omega z) i = true := by
    rw [triHexPlanarFiniteStarConfigEquiv_direction]
    rw [ha]
    have := huv.2
    rw [← hedge] at this
    change (extendActive (triHexPlanarFiniteStarGraph n) omega)
      ((triHexPlanarFiniteStarEdgeEquiv n (z, i)).1) = true at this
    rw [extendActive_apply, ha] at this
    exact this
  have hselected := starFKRepresentativeDirection_open_of_open
    (triHexPlanarFiniteStarConfigEquiv n omega z) i hopen
  have hconnects : (starFKLocalConnectivity
      (triHexPlanarFiniteStarConfigEquiv n omega z)).Connects
        (starFKRepresentativeDirection
          (triHexPlanarFiniteStarConfigEquiv n omega z)) i :=
    (starFKLocalConnectivity_connects_iff _ _ _).2
      (Or.inr ⟨hselected, hopen⟩)
  have hreach := triHexFKTerminalSectorGraph_reachable_of_connects
    (triHexPlanarFiniteTerminalMap n)
    (fun z => starFKLocalConnectivity
      (triHexPlanarFiniteStarConfigEquiv n omega z)) z _ _ hconnects
  rw [Sym2.eq_iff] at hedge
  rcases hedge with ⟨hu, hv⟩ | ⟨hv, hu⟩
  · rw [← hu, ← hv]
    simpa [triHexPlanarFiniteStarRepresentative,
      triHexPlanarFiniteStarSectorGraph] using hreach
  · rw [← hu, ← hv]
    simpa [triHexPlanarFiniteStarRepresentative,
      triHexPlanarFiniteStarSectorGraph] using hreach.symm


theorem triHexPlanarFiniteStar_sector_adj_openSub_reachable
    (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet)
    {x y : TriHexPlanarFiniteTerminal n}
    (hxy : (triHexPlanarFiniteStarSectorGraph n omega).Adj x y) :
    (openSub (triHexPlanarFiniteStarGraph n)
      (extendActive (triHexPlanarFiniteStarGraph n) omega)).Reachable
        (Sum.inr x) (Sum.inr y) := by
  rw [triHexPlanarFiniteStarSectorGraph, triHexFKTerminalSectorGraph,
    SimpleGraph.fromEdgeSet_adj] at hxy
  obtain ⟨⟨z, i, j, hconnects, hedge⟩, _⟩ := hxy
  have hreach := triHexPlanarFiniteStar_openSub_reachable_of_connects
    n omega z i j hconnects
  rw [Sym2.eq_iff] at hedge
  rcases hedge with ⟨hxi, hyj⟩ | ⟨hxj, hyi⟩
  · simpa [hxi, hyj] using hreach
  · simpa [hxj, hyi] using hreach.symm


theorem triHexPlanarFiniteStar_openSub_white_reachable_iff_sector
    (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet)
    (x y : TriHexPlanarFiniteTerminal n) :
    (openSub (triHexPlanarFiniteStarGraph n)
      (extendActive (triHexPlanarFiniteStarGraph n) omega)).Reachable
        (Sum.inr x) (Sum.inr y) ↔
      (triHexPlanarFiniteStarSectorGraph n omega).Reachable x y := by
  constructor
  · intro h
    have hc := reachable_map_of_adj_reachable _ _
      (triHexPlanarFiniteStarRepresentative n omega)
      (fun _ _ hab =>
        triHexPlanarFiniteStar_openSub_adj_representative_reachable n omega hab) h
    simpa [triHexPlanarFiniteStarRepresentative] using hc
  · intro h
    exact reachable_map_of_adj_reachable _ _ Sum.inr
      (fun _ _ hab =>
        triHexPlanarFiniteStar_sector_adj_openSub_reachable n omega hab) h


end
end StatMech.FK.PeriodicPlanar
