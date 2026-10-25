/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKGlobalSweep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKExternalWeight
import Theorem.StatisticalMechanics.Code.FK.TriHexFKGlobalSweep.Part2
open Finset
open scoped BigOperators


namespace StatMech.FK.PeriodicPlanar

open Universality


noncomputable def triangleFKGlobalSweepRatio
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (y0 y1 y2 : Real)
    (external observable : (ι → ThreeTerminalConnectivity) → Real) : Real :=
  triangleFKGlobalSweepSum y0 y1 y2
      (fun sector => external sector * observable sector) /
    triangleFKGlobalSweepSum y0 y1 y2 external


noncomputable def starFKGlobalSweepRatio
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q y0 y1 y2 : Real)
    (external observable : (ι → ThreeTerminalConnectivity) → Real) : Real :=
  starFKGlobalSweepSum q y0 y1 y2
      (fun sector => external sector * observable sector) /
    starFKGlobalSweepSum q y0 y1 y2 external


end StatMech.FK.PeriodicPlanar
