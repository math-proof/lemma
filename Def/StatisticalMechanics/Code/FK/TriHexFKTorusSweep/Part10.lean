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
import Theorem.StatisticalMechanics.Code.FK.TriHexFKTorusSweep.Part9


namespace StatMech.FK.PeriodicPlanar

open Universality

open scoped BigOperators


noncomputable def hexagonalTorusConnectedComponentEquiv
    (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (hexagonalTorusGraph L).edgeSet) :
    (openSub (hexagonalTorusGraph L)
      (extendActive (hexagonalTorusGraph L) omega)).ConnectedComponent ≃
      (hexagonalTorusTerminalSectorGraph L omega).ConnectedComponent ⊕
        HexagonalTorusIsolatedCenter L omega where
  toFun := SimpleGraph.ConnectedComponent.lift
    (hexagonalTorusVertexComponentLabel L omega) (by
      intro x y path _hpath
      clear _hpath
      induction path with
      | nil => rfl
      | cons h rest ih =>
          exact (hexagonalTorusVertexComponentLabel_eq_of_adj L omega h).trans ih)
  invFun
    | Sum.inl component => SimpleGraph.ConnectedComponent.lift
        (fun z => (openSub (hexagonalTorusGraph L)
          (extendActive (hexagonalTorusGraph L) omega)).connectedComponentMk (z, true))
        (by
          intro x y path _hpath
          apply SimpleGraph.ConnectedComponent.sound
          exact (hexagonalTorus_openSub_white_reachable_iff_terminalSectorGraph
            L omega x y).mpr path.reachable) component
    | Sum.inr z => (openSub (hexagonalTorusGraph L)
        (extendActive (hexagonalTorusGraph L) omega)).connectedComponentMk (z.1, false)
  left_inv component := by
    induction component using SimpleGraph.ConnectedComponent.ind with
    | h v =>
      rcases v with ⟨z, b⟩
      cases b
      · by_cases hclosed : hexagonalTorusActiveConfigEquiv L omega z =
            (false, false, false)
        · simp [hexagonalTorusVertexComponentLabel, hclosed]
        · simp only [SimpleGraph.ConnectedComponent.lift_mk,
            hexagonalTorusVertexComponentLabel, hclosed, dite_false]
          apply SimpleGraph.ConnectedComponent.sound
          apply SimpleGraph.Adj.reachable
          simpa [hexagonalTorusOpenRepresentative] using
            (hexagonalTorus_openSub_adj_spoke L omega z
              (starFKRepresentativeDirection
                (hexagonalTorusActiveConfigEquiv L omega z))
              (starFKRepresentativeDirection_open_of_not_closed _ hclosed)).symm
      · simp [hexagonalTorusVertexComponentLabel]
  right_inv label := by
    rcases label with component | z
    · induction component using SimpleGraph.ConnectedComponent.ind with
      | h x => simp [hexagonalTorusVertexComponentLabel]
    · simp [hexagonalTorusVertexComponentLabel, z.2]


end StatMech.FK.PeriodicPlanar
