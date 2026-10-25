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
import Def.StatisticalMechanics.Code.FK.TriHexFKTorusSweep.Part9


namespace StatMech.FK.PeriodicPlanar

open Universality

open scoped BigOperators


theorem hexagonalTorusVertexComponentLabel_eq_of_adj
    (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (hexagonalTorusGraph L).edgeSet)
    {u v : HexTorusVertex L}
    (huv : (openSub (hexagonalTorusGraph L)
      (extendActive (hexagonalTorusGraph L) omega)).Adj u v) :
    hexagonalTorusVertexComponentLabel L omega u =
      hexagonalTorusVertexComponentLabel L omega v := by
  obtain ⟨z, i, hi, horient⟩ :=
    hexagonalTorus_openSub_adj_eq_spoke L omega huv
  have hnot : hexagonalTorusActiveConfigEquiv L omega z ≠
      (false, false, false) := by
    intro hclosed
    rw [hclosed] at hi
    fin_cases i <;> simp [triHexLocalDirection] at hi
  have hreach := hexagonalTorus_openSub_adj_representative_reachable L omega huv
  have hcomponent :
      (hexagonalTorusTerminalSectorGraph L omega).connectedComponentMk
          (hexagonalTorusOpenRepresentative L omega u) =
        (hexagonalTorusTerminalSectorGraph L omega).connectedComponentMk
          (hexagonalTorusOpenRepresentative L omega v) :=
    SimpleGraph.ConnectedComponent.sound hreach
  rcases horient with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [hexagonalTorusVertexComponentLabel, dif_neg hnot]
    exact congrArg Sum.inl hcomponent
  · simp only [hexagonalTorusVertexComponentLabel, dif_neg hnot]
    exact congrArg Sum.inl hcomponent


end StatMech.FK.PeriodicPlanar
