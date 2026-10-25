/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredGraphs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredSweep.Part3
import Theorem.StatisticalMechanics.Code.FK.TriHexFKTorusSweep.Part15
import Def.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredGraphs.Part13
open Finset Set


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open Universality

noncomputable section

theorem triHexPlanarFiniteStar_wired_white_reachable_iff_sector
    (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet)
    (x y : TriHexPlanarFiniteTerminal n) :
    (wiredGraph (triHexPlanarFiniteStarGraph n)
      (triHexPlanarFiniteStarBoundary n)
      (extendActive (triHexPlanarFiniteStarGraph n) omega)).Reachable
        (Sum.inr x) (Sum.inr y) ↔
      (triHexPlanarFiniteStarWiredSectorGraph n omega).Reachable x y := by
  let Gopen := openSub (triHexPlanarFiniteStarGraph n)
    (extendActive (triHexPlanarFiniteStarGraph n) omega)
  let Gsector := triHexPlanarFiniteStarSectorGraph n omega
  let Kstar := boundaryCliqueGraph (triHexPlanarFiniteStarBoundary n)
  let Kterminal := boundaryCliqueGraph (triHexPlanarFiniteBoundary n)
  have hopen : openGraph (triHexPlanarFiniteStarGraph n)
      (extendActive (triHexPlanarFiniteStarGraph n) omega) = Gopen := rfl
  have hsector : triHexPlanarFiniteStarWiredSectorGraph n omega =
      Gsector ⊔ Kterminal := rfl
  rw [wiredGraph, hopen, hsector]
  constructor
  · intro h
    have hc := reachable_map_of_adj_reachable (Gopen ⊔ Kstar)
      (Gsector ⊔ Kterminal)
      (triHexPlanarFiniteStarRepresentative n omega) (fun u v huv => by
        rw [SimpleGraph.sup_adj] at huv
        rcases huv with hopenEdge | hboundary
        · exact (triHexPlanarFiniteStar_openSub_adj_representative_reachable
            n omega hopenEdge).mono le_sup_left
        · rw [boundaryCliqueGraph_adj] at hboundary
          rcases u with u | u <;> rcases v with v | v
          · exact (hboundary.2.1.elim)
          · exact (hboundary.2.1.elim)
          · exact (hboundary.2.2.elim)
          · change (Gsector ⊔ Kterminal).Reachable u v
            have hb : Kterminal.Adj u v := by
              change (boundaryCliqueGraph
                (triHexPlanarFiniteBoundary n)).Adj u v
              rw [boundaryCliqueGraph_adj]
              exact ⟨fun huv => hboundary.1 (congrArg Sum.inr huv),
                hboundary.2.1, hboundary.2.2⟩
            have hb' : (Gsector ⊔ Kterminal).Adj u v :=
              (show Kterminal ≤ Gsector ⊔ Kterminal from le_sup_right) hb
            exact hb'.reachable) h
    simpa [triHexPlanarFiniteStarRepresentative] using hc
  · intro h
    exact reachable_map_of_adj_reachable (Gsector ⊔ Kterminal)
      (Gopen ⊔ Kstar) Sum.inr (fun u v huv => by
        rw [SimpleGraph.sup_adj] at huv
        rcases huv with hsectorEdge | hboundary
        · exact (triHexPlanarFiniteStar_openSub_white_reachable_iff_sector
            n omega u v).mpr hsectorEdge.reachable |>.mono le_sup_left
        · change (Gopen ⊔ Kstar).Reachable (Sum.inr u) (Sum.inr v)
          have hb : Kstar.Adj (Sum.inr u) (Sum.inr v) := by
            change (boundaryCliqueGraph
              (triHexPlanarFiniteStarBoundary n)).Adj (Sum.inr u) (Sum.inr v)
            rw [boundaryCliqueGraph_adj]
            change (boundaryCliqueGraph
              (triHexPlanarFiniteBoundary n)).Adj u v at hboundary
            rw [boundaryCliqueGraph_adj] at hboundary
            exact ⟨fun huv => hboundary.1 (Sum.inr.inj huv),
              hboundary.2.1, hboundary.2.2⟩
          have hb' : (Gopen ⊔ Kstar).Adj (Sum.inr u) (Sum.inr v) :=
            (show Kstar ≤ Gopen ⊔ Kstar from le_sup_right) hb
          exact hb'.reachable) h


theorem triHexPlanarFiniteStar_openSub_adj_eq_spoke
    (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet)
    {u v : TriHexPlanarFiniteStarVertex n}
    (huv : (openSub (triHexPlanarFiniteStarGraph n)
      (extendActive (triHexPlanarFiniteStarGraph n) omega)).Adj u v) :
    ∃ z i, triHexLocalDirection
        (triHexPlanarFiniteStarConfigEquiv n omega z) i = true ∧
      ((u = Sum.inl z ∧
          v = Sum.inr (triHexPlanarFiniteTerminalMap n z i)) ∨
        (v = Sum.inl z ∧
          u = Sum.inr (triHexPlanarFiniteTerminalMap n z i))) := by
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
  refine ⟨z, i, hopen, ?_⟩
  rw [Sym2.eq_iff] at hedge
  rcases hedge with ⟨hu, hv⟩ | ⟨hv, hu⟩
  · exact Or.inl ⟨hu.symm, hv.symm⟩
  · exact Or.inr ⟨hv.symm, hu.symm⟩


end
end StatMech.FK.PeriodicPlanar
