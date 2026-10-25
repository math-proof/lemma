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
import Def.StatisticalMechanics.Code.FK.TriHexFKTorusSweep


namespace StatMech.FK.PeriodicPlanar

open Universality

open scoped BigOperators


theorem triHexTorusTriangleSweepEdge_val
    (L : ℕ) [Fact (2 < L)] (z : TorusSite L) (i : Fin 3) :
    ((triHexTorusTriangleSweepEdgeEquiv L (z, i) :
      (triangularTorusGraph L).edgeSet) : Sym2 (TorusSite L)) =
        s(triHexTorusCellTerminal L z (triHexTriangleEdgeTerminal1 i),
          triHexTorusCellTerminal L z (triHexTriangleEdgeTerminal2 i)) := by
  fin_cases i <;>
    simp [triHexTorusTriangleSweepEdgeEquiv,
      triHexTorusTriangleIndexEquiv, triHexTorusTriangleEdgeBaseShift,
      triangularTorusEdgeChartEquiv, triangularTorusEdgeChart,
      triangularTorusIndexedEdge, triHexTorusCellTerminal,
      triHexTriangleEdgeTerminal1, triHexTriangleEdgeTerminal2,
      triangularTorusStep, hexagonalTorusStep, Prod.ext_iff, add_assoc]


theorem triHexTorusStarSweepEdge_val
    (L : ℕ) [Fact (2 < L)] (z : TorusSite L) (i : Fin 3) :
    ((triHexTorusStarSweepEdgeEquiv L (z, i) :
      (hexagonalTorusGraph L).edgeSet) : Sym2 (HexTorusVertex L)) =
        s((z, false), (triHexTorusCellTerminal L z i, true)) := by
  rfl


theorem triangleFKLocalConnectivity_connects_of_direction
    (config : LocalConfig) (i : Fin 3)
    (h : triHexLocalDirection config i = true) :
    (triangleFKLocalConnectivity config).Connects
      (triHexTriangleEdgeTerminal1 i) (triHexTriangleEdgeTerminal2 i) := by
  rcases config with ⟨b0, b1, b2⟩
  fin_cases b0 <;> fin_cases b1 <;> fin_cases b2 <;> fin_cases i <;>
    simp_all [triHexLocalDirection, triangleFKLocalConnectivity,
      triHexTriangleEdgeTerminal1, triHexTriangleEdgeTerminal2,
      ThreeTerminalConnectivity.Connects]


end StatMech.FK.PeriodicPlanar
