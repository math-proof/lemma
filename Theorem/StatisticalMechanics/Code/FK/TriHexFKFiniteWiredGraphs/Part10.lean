/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredGraphs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredSweep.Part3
import Theorem.StatisticalMechanics.Code.FK.TriHexFKTorusSweep.Part15
import Instance.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredGraphs.Part3
open Finset Set


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open Universality

noncomputable section

theorem triHexPlanarFiniteStar_openSub_adj_spoke
    (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet)
    (z : TriHexPlanarFiniteCell n) (i : Fin 3)
    (hopen : triHexLocalDirection
      (triHexPlanarFiniteStarConfigEquiv n omega z) i = true) :
    (openSub (triHexPlanarFiniteStarGraph n)
      (extendActive (triHexPlanarFiniteStarGraph n) omega)).Adj
        (Sum.inl z)
        (Sum.inr (triHexPlanarFiniteTerminalMap n z i)) := by
  rw [openSub_adj]
  constructor
  · rw [← SimpleGraph.mem_edgeSet]
    exact (triHexPlanarFiniteStarEdgeEquiv n (z, i)).2
  · change (extendActive (triHexPlanarFiniteStarGraph n) omega)
      (triHexPlanarFiniteStarEdge n (z, i)) = true
    rw [show triHexPlanarFiniteStarEdge n (z, i) =
        (triHexPlanarFiniteStarEdgeEquiv n (z, i)).1 from rfl,
      extendActive_apply]
    exact (triHexPlanarFiniteStarConfigEquiv_direction n omega z i).symm.trans
      hopen


theorem triHexPlanarFiniteStar_openSub_reachable_of_connects
    (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet)
    (z : TriHexPlanarFiniteCell n) (i j : Fin 3)
    (hconnects : (starFKLocalConnectivity
      (triHexPlanarFiniteStarConfigEquiv n omega z)).Connects i j) :
    (openSub (triHexPlanarFiniteStarGraph n)
      (extendActive (triHexPlanarFiniteStarGraph n) omega)).Reachable
        (Sum.inr (triHexPlanarFiniteTerminalMap n z i))
        (Sum.inr (triHexPlanarFiniteTerminalMap n z j)) := by
  rcases (starFKLocalConnectivity_connects_iff
    (triHexPlanarFiniteStarConfigEquiv n omega z) i j).mp hconnects with
    rfl | ⟨hi, hj⟩
  · exact SimpleGraph.Reachable.refl _
  · exact (SimpleGraph.Adj.reachable
      (triHexPlanarFiniteStar_openSub_adj_spoke n omega z i hi)).symm.trans
        (SimpleGraph.Adj.reachable
          (triHexPlanarFiniteStar_openSub_adj_spoke n omega z j hj))


end
end StatMech.FK.PeriodicPlanar
