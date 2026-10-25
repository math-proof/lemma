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
import Def.StatisticalMechanics.Code.FK.TriHexFKTorusSweep.Part5


namespace StatMech.FK.PeriodicPlanar

open Universality

open scoped BigOperators


theorem triHexFKTerminalSectorGraph_reachable_of_connects
    {I V : Type*} [Fintype I] [DecidableEq I] [DecidableEq V]
    (terminal : I → Fin 3 → V)
    (sector : I → ThreeTerminalConnectivity)
    (cell : I) (i j : Fin 3) (hconnects : (sector cell).Connects i j) :
    (triHexFKTerminalSectorGraph terminal sector).Reachable
      (terminal cell i) (terminal cell j) := by
  by_cases hterm : terminal cell i = terminal cell j
  · simpa [hterm] using
      (SimpleGraph.Reachable.refl (G := triHexFKTerminalSectorGraph terminal sector)
        (terminal cell i))
  · apply SimpleGraph.Adj.reachable
    rw [triHexFKTerminalSectorGraph, SimpleGraph.fromEdgeSet_adj]
    exact ⟨⟨cell, i, j, hconnects, rfl⟩, hterm⟩


end StatMech.FK.PeriodicPlanar
