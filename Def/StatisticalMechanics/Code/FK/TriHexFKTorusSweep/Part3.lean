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
import Theorem.StatisticalMechanics.Code.FK.TriHexFKTorusSweep.Part2


namespace StatMech.FK.PeriodicPlanar

open Universality

open scoped BigOperators


noncomputable def triangularTorusTerminalSectorGraph
    (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (triangularTorusGraph L).edgeSet) :
    SimpleGraph (TorusSite L) :=
  triHexFKTerminalSectorGraph (triHexTorusCellTerminal L)
    (fun z => triangleFKLocalConnectivity
      (triangularTorusActiveConfigEquiv L omega z))


end StatMech.FK.PeriodicPlanar
