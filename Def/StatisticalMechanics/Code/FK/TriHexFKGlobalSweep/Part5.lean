/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKGlobalSweep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKExternalWeight
import Theorem.StatisticalMechanics.Code.FK.TriHexFKGlobalSweep.Part4
open Finset
open scoped BigOperators


namespace StatMech.FK.PeriodicPlanar

open Universality


def triHexFKTerminalSectorGraph
    {ι V : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq V]
    (terminal : ι → Fin 3 → V)
    (sector : ι → ThreeTerminalConnectivity) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet {edge | ∃ cell i j,
    (sector cell).Connects i j ∧ edge = s(terminal cell i, terminal cell j)}


noncomputable def triHexFKTerminalTwoPointObservable
    {ι V : Type*} [Fintype ι] [DecidableEq ι] [Fintype V] [DecidableEq V]
    (terminal : ι → Fin 3 → V) (x y : V)
    (sector : ι → ThreeTerminalConnectivity) : Real :=
  by
    classical
    exact if (triHexFKTerminalSectorGraph terminal sector).Reachable x y then 1 else 0


end StatMech.FK.PeriodicPlanar
