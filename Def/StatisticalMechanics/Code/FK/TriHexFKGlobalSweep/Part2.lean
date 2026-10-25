/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKGlobalSweep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKExternalWeight
import Theorem.StatisticalMechanics.Code.FK.TriHexFKGlobalSweep
open Finset
open scoped BigOperators


namespace StatMech.FK.PeriodicPlanar

open Universality


def triangleFKGlobalSweepSum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (y0 y1 y2 : Real)
    (external : (ι → ThreeTerminalConnectivity) → Real) : Real :=
  ∑ sector : ι → ThreeTerminalConnectivity,
    external sector * ∏ i, triangleFKTerminalWeight y0 y1 y2 (sector i)


def starFKGlobalSweepSum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q y0 y1 y2 : Real)
    (external : (ι → ThreeTerminalConnectivity) → Real) : Real :=
  ∑ sector : ι → ThreeTerminalConnectivity,
    external sector * ∏ i, starFKTerminalWeight q y0 y1 y2 (sector i)


def triangleFKGlobalConfigSum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (y0 y1 y2 : Real)
    (external : (ι → ThreeTerminalConnectivity) → Real) : Real :=
  ∑ config : ι → LocalConfig,
    external (fun i => triangleFKLocalConnectivity (config i)) *
      ∏ i, triangleFKLocalOddsWeight y0 y1 y2 (config i)


def starFKGlobalConfigSum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q y0 y1 y2 : Real)
    (external : (ι → ThreeTerminalConnectivity) → Real) : Real :=
  ∑ config : ι → LocalConfig,
    external (fun i => starFKLocalConnectivity (config i)) *
      ∏ i, starFKLocalOddsWeight q y0 y1 y2 (config i)


end StatMech.FK.PeriodicPlanar
