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
import Theorem.StatisticalMechanics.Code.FK.TriHexFKTorusSweep.Part14


namespace StatMech.FK.PeriodicPlanar

open Universality

open scoped BigOperators


noncomputable def triangularTorusActiveTwoPointIndicator
    (L : ℕ) [Fact (2 < L)] (x y : TorusSite L)
    (omega : ConfigSpace (triangularTorusGraph L).edgeSet) : ℝ :=
  if (openSub (triangularTorusGraph L)
    (extendActive (triangularTorusGraph L) omega)).Reachable x y then 1 else 0


noncomputable def hexagonalTorusActiveWhiteTwoPointIndicator
    (L : ℕ) [Fact (2 < L)] (x y : TorusSite L)
    (omega : ConfigSpace (hexagonalTorusGraph L).edgeSet) : ℝ :=
  if (openSub (hexagonalTorusGraph L)
    (extendActive (hexagonalTorusGraph L) omega)).Reachable
      (x, true) (y, true) then 1 else 0

end StatMech.FK.PeriodicPlanar
