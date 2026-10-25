/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredGraphs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredSweep.Part3
import Theorem.StatisticalMechanics.Code.FK.TriHexFKTorusSweep.Part15
import Def.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredGraphs.Part10
open Finset Set


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open Universality

noncomputable section

theorem triHexPlanarFiniteTriangle_wired_reachable_iff_sector
    (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteTriangleGraph n).edgeSet)
    (x y : TriHexPlanarFiniteTerminal n) :
    (wiredGraph (triHexPlanarFiniteTriangleGraph n)
      (triHexPlanarFiniteBoundary n)
      (extendActive (triHexPlanarFiniteTriangleGraph n) omega)).Reachable x y ↔
      (triHexPlanarFiniteTriangleWiredSectorGraph n omega).Reachable x y := by
  let Gopen := openSub (triHexPlanarFiniteTriangleGraph n)
    (extendActive (triHexPlanarFiniteTriangleGraph n) omega)
  let Gsector := triHexPlanarFiniteTriangleSectorGraph n omega
  let K := boundaryCliqueGraph (triHexPlanarFiniteBoundary n)
  have hopen : openGraph (triHexPlanarFiniteTriangleGraph n)
      (extendActive (triHexPlanarFiniteTriangleGraph n) omega) = Gopen := rfl
  have hsector : triHexPlanarFiniteTriangleWiredSectorGraph n omega =
      Gsector ⊔ K := rfl
  rw [wiredGraph, hopen, hsector]
  constructor
  · intro h
    exact reachable_map_of_adj_reachable (Gopen ⊔ K) (Gsector ⊔ K) id
      (fun _ _ hab => by
        rw [SimpleGraph.sup_adj] at hab
        rcases hab with hopenEdge | hboundary
        · exact (triHexPlanarFiniteTriangle_openSub_reachable_iff_sector
            n omega _ _).mp hopenEdge.reachable |>.mono le_sup_left
        · exact hboundary.reachable.mono le_sup_right) h
  · intro h
    exact reachable_map_of_adj_reachable (Gsector ⊔ K) (Gopen ⊔ K) id
      (fun _ _ hab => by
        rw [SimpleGraph.sup_adj] at hab
        rcases hab with hsectorEdge | hboundary
        · exact (triHexPlanarFiniteTriangle_openSub_reachable_iff_sector
            n omega _ _).mpr hsectorEdge.reachable |>.mono le_sup_left
        · exact hboundary.reachable.mono le_sup_right) h


theorem triHexPlanarFiniteTriangle_numClustersWired_eq_sector
    (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteTriangleGraph n).edgeSet) :
    numClustersWired (triHexPlanarFiniteTriangleGraph n)
        (triHexPlanarFiniteBoundary n)
        (extendActive (triHexPlanarFiniteTriangleGraph n) omega) =
      Nat.card
        (triHexPlanarFiniteTriangleWiredSectorGraph n omega).ConnectedComponent := by
  unfold numClustersWired
  exact Nat.card_congr
    (connectedComponentEquivOfReachableIff _ _
      (triHexPlanarFiniteTriangle_wired_reachable_iff_sector n omega))


end
end StatMech.FK.PeriodicPlanar
