/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredGraphs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredSweep.Part3
import Theorem.StatisticalMechanics.Code.FK.TriHexFKTorusSweep.Part15
import Def.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredGraphs.Part16
open Finset Set


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open Universality

noncomputable section

theorem triHexPlanarFiniteStar_numClustersWired_eq_sector_add_isolated
    (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet) :
    numClustersWired (triHexPlanarFiniteStarGraph n)
        (triHexPlanarFiniteStarBoundary n)
        (extendActive (triHexPlanarFiniteStarGraph n) omega) =
      Nat.card
          (triHexPlanarFiniteStarWiredSectorGraph n omega).ConnectedComponent +
        Fintype.card (TriHexPlanarFiniteStarIsolatedCenter n omega) := by
  unfold numClustersWired
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    ← Fintype.card_sum]
  exact Fintype.card_congr
    (triHexPlanarFiniteStarConnectedComponentEquiv n omega)

end
end StatMech.FK.PeriodicPlanar
