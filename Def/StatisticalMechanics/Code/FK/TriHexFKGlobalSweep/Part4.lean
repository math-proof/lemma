/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKGlobalSweep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKExternalWeight
import Theorem.StatisticalMechanics.Code.FK.TriHexFKGlobalSweep.Part3
open Finset
open scoped BigOperators


namespace StatMech.FK.PeriodicPlanar

open Universality


def ThreeTerminalConnectivity.Connects
    (connectivity : ThreeTerminalConnectivity) (i j : Fin 3) : Prop :=
  i = j ∨ match connectivity with
    | .separate => False
    | .pair01 => (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)
    | .pair12 => (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1)
    | .pair20 => (i = 2 ∧ j = 0) ∨ (i = 0 ∧ j = 2)
    | .together => True

end StatMech.FK.PeriodicPlanar
