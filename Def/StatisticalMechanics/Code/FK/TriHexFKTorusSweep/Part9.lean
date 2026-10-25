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
import Theorem.StatisticalMechanics.Code.FK.TriHexFKTorusSweep.Part8


namespace StatMech.FK.PeriodicPlanar

open Universality

open scoped BigOperators


noncomputable def hexagonalTorusVertexComponentLabel
    (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (hexagonalTorusGraph L).edgeSet) :
    HexTorusVertex L →
      (hexagonalTorusTerminalSectorGraph L omega).ConnectedComponent ⊕
        HexagonalTorusIsolatedCenter L omega
  | (z, true) => Sum.inl
      ((hexagonalTorusTerminalSectorGraph L omega).connectedComponentMk z)
  | (z, false) => if h : hexagonalTorusActiveConfigEquiv L omega z =
        (false, false, false) then
      Sum.inr ⟨z, h⟩
    else
      Sum.inl ((hexagonalTorusTerminalSectorGraph L omega).connectedComponentMk
        (hexagonalTorusOpenRepresentative L omega (z, false)))


end StatMech.FK.PeriodicPlanar
