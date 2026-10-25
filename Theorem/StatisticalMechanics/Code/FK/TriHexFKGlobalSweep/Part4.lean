/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKGlobalSweep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKExternalWeight
import Def.StatisticalMechanics.Code.FK.TriHexFKGlobalSweep.Part4
open Finset
open scoped BigOperators


namespace StatMech.FK.PeriodicPlanar

open Universality


theorem ThreeTerminalConnectivity.connects_symm
    (connectivity : ThreeTerminalConnectivity) (i j : Fin 3) :
    connectivity.Connects i j ↔ connectivity.Connects j i := by
  fin_cases connectivity <;> fin_cases i <;> fin_cases j <;>
    simp [ThreeTerminalConnectivity.Connects]


end StatMech.FK.PeriodicPlanar
