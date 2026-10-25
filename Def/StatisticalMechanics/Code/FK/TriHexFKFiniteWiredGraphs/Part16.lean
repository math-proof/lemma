/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredGraphs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredSweep.Part3
import Theorem.StatisticalMechanics.Code.FK.TriHexFKTorusSweep.Part15
import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredGraphs.Part14
open Finset Set


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open Universality

noncomputable section

def triHexPlanarFiniteStarConnectedComponentEquiv (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet) :
    (wiredGraph (triHexPlanarFiniteStarGraph n)
      (triHexPlanarFiniteStarBoundary n)
      (extendActive (triHexPlanarFiniteStarGraph n) omega)).ConnectedComponent ≃
      (triHexPlanarFiniteStarWiredSectorGraph n omega).ConnectedComponent ⊕
        TriHexPlanarFiniteStarIsolatedCenter n omega where
  toFun := SimpleGraph.ConnectedComponent.lift
    (triHexPlanarFiniteStarVertexComponentLabel n omega) (by
      intro x y path _hpath
      clear _hpath
      induction path with
      | nil => rfl
      | cons h rest ih =>
          exact (triHexPlanarFiniteStarVertexComponentLabel_eq_of_wired_adj
            n omega h).trans ih)
  invFun
    | Sum.inl component => SimpleGraph.ConnectedComponent.lift
        (fun v => (wiredGraph (triHexPlanarFiniteStarGraph n)
          (triHexPlanarFiniteStarBoundary n)
          (extendActive (triHexPlanarFiniteStarGraph n) omega)).connectedComponentMk
            (Sum.inr v))
        (by
          intro x y path _
          apply SimpleGraph.ConnectedComponent.sound
          exact (triHexPlanarFiniteStar_wired_white_reachable_iff_sector
            n omega x y).mpr path.reachable) component
    | Sum.inr z => (wiredGraph (triHexPlanarFiniteStarGraph n)
        (triHexPlanarFiniteStarBoundary n)
        (extendActive (triHexPlanarFiniteStarGraph n) omega)).connectedComponentMk
          (Sum.inl z.1)
  left_inv component := by
    induction component using SimpleGraph.ConnectedComponent.ind with
    | h v =>
      rcases v with z | v
      · by_cases hclosed : triHexPlanarFiniteStarConfigEquiv n omega z =
            (false, false, false)
        · simp [triHexPlanarFiniteStarVertexComponentLabel, hclosed]
        · simp only [SimpleGraph.ConnectedComponent.lift_mk,
            triHexPlanarFiniteStarVertexComponentLabel, hclosed, dite_false]
          apply SimpleGraph.ConnectedComponent.sound
          apply SimpleGraph.Adj.reachable
          apply (show openGraph (triHexPlanarFiniteStarGraph n)
              (extendActive (triHexPlanarFiniteStarGraph n) omega) ≤
            wiredGraph (triHexPlanarFiniteStarGraph n)
              (triHexPlanarFiniteStarBoundary n)
              (extendActive (triHexPlanarFiniteStarGraph n) omega) from le_sup_left)
          exact (triHexPlanarFiniteStar_openSub_adj_spoke n omega z
            (starFKRepresentativeDirection
              (triHexPlanarFiniteStarConfigEquiv n omega z))
            (starFKRepresentativeDirection_open_of_not_closed _ hclosed)).symm
      · simp [triHexPlanarFiniteStarVertexComponentLabel]
  right_inv label := by
    rcases label with component | z
    · induction component using SimpleGraph.ConnectedComponent.ind with
      | h v => simp [triHexPlanarFiniteStarVertexComponentLabel]
    · simp [triHexPlanarFiniteStarVertexComponentLabel, z.2]


end
end StatMech.FK.PeriodicPlanar
