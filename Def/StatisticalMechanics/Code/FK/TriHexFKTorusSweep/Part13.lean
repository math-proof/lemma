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
import Theorem.StatisticalMechanics.Code.FK.TriHexFKTorusSweep.Part12


namespace StatMech.FK.PeriodicPlanar

open Universality

open scoped BigOperators


noncomputable def triHexTorusSectorClusterWeight
    (L : ℕ) [Fact (2 < L)] (q : ℝ)
    (sector : TorusSite L → ThreeTerminalConnectivity) : ℝ :=
  q ^ Fintype.card
    (triHexFKTerminalSectorGraph (triHexTorusCellTerminal L) sector).ConnectedComponent


end StatMech.FK.PeriodicPlanar
