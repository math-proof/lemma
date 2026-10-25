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
import Def.StatisticalMechanics.Code.FK.TriHexFKTorusSweep.Part4


namespace StatMech.FK.PeriodicPlanar

open Universality

open scoped BigOperators


theorem reachable_map_of_adj_reachable
    {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
    (f : V → W) (hedge : ∀ x y, G.Adj x y → H.Reachable (f x) (f y))
    {x y : V} (hxy : G.Reachable x y) : H.Reachable (f x) (f y) := by
  obtain ⟨walk⟩ := hxy
  induction walk with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons h rest ih => exact (hedge _ _ h).trans ih


theorem triangularTorus_numClusters_eq_terminalSector
    (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (triangularTorusGraph L).edgeSet) :
    numClusters (triangularTorusGraph L)
        (extendActive (triangularTorusGraph L) omega) =
      Fintype.card (triangularTorusTerminalSectorGraph L omega).ConnectedComponent := by
  unfold numClusters
  exact Fintype.card_congr
    (connectedComponentEquivOfReachableIff _ _
      (triangularTorus_openSub_reachable_iff_terminalSectorGraph L omega))


theorem starFKLocalConnectivity_connects_iff
    (config : LocalConfig) (i j : Fin 3) :
    (starFKLocalConnectivity config).Connects i j ↔
      i = j ∨ (triHexLocalDirection config i = true ∧
        triHexLocalDirection config j = true) := by
  rcases config with ⟨b0, b1, b2⟩
  fin_cases b0 <;> fin_cases b1 <;> fin_cases b2 <;>
    fin_cases i <;> fin_cases j <;>
    simp [starFKLocalConnectivity, ThreeTerminalConnectivity.Connects,
      triHexLocalDirection]


theorem hexagonalTorus_openSub_reachable_of_connects
    (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (hexagonalTorusGraph L).edgeSet)
    (z : TorusSite L) (i j : Fin 3)
    (hconnects : (starFKLocalConnectivity
      (hexagonalTorusActiveConfigEquiv L omega z)).Connects i j) :
    (openSub (hexagonalTorusGraph L)
      (extendActive (hexagonalTorusGraph L) omega)).Reachable
        (triHexTorusCellTerminal L z i, true)
        (triHexTorusCellTerminal L z j, true) := by
  rcases (starFKLocalConnectivity_connects_iff
    (hexagonalTorusActiveConfigEquiv L omega z) i j).mp hconnects with
    rfl | ⟨hi, hj⟩
  · exact SimpleGraph.Reachable.refl _
  · exact (SimpleGraph.Adj.reachable
      (hexagonalTorus_openSub_adj_spoke L omega z i hi)).symm.trans
        (SimpleGraph.Adj.reachable
          (hexagonalTorus_openSub_adj_spoke L omega z j hj))


end StatMech.FK.PeriodicPlanar
