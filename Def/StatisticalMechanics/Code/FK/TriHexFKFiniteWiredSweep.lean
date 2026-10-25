/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredSweep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKGlobalSweep.Part5
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarGraph.Part18
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
open Finset


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

noncomputable section

def triHexFKTerminalWiredGraph
    {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype V] [DecidableEq V]
    (terminal : ι → Fin 3 → V) (boundary : V → Prop)
    [DecidablePred boundary]
    (sector : ι → ThreeTerminalConnectivity) : SimpleGraph V :=
  triHexFKTerminalSectorGraph terminal sector ⊔ boundaryCliqueGraph boundary


def triHexFKTerminalWiredExternal
    {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype V] [DecidableEq V]
    (q : Real) (terminal : ι → Fin 3 → V) (boundary : V → Prop)
    [DecidablePred boundary]
    (sector : ι → ThreeTerminalConnectivity) : Real :=
  q ^ Nat.card (triHexFKTerminalWiredGraph terminal boundary sector).ConnectedComponent


def triHexFKTerminalBoundaryReachObservable
    {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype V] [DecidableEq V]
    (terminal : ι → Fin 3 → V) (boundary : V → Prop)
    [DecidablePred boundary] (root : V)
    (sector : ι → ThreeTerminalConnectivity) : Real := by
  classical
  exact if ∃ y : V, boundary y ∧
      (triHexFKTerminalSectorGraph terminal sector).Reachable root y then 1 else 0


def triangleFKFiniteWiredBoundaryReachRatio
    {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype V] [DecidableEq V]
    (q y0 y1 y2 : Real) (terminal : ι → Fin 3 → V)
    (boundary : V → Prop) [DecidablePred boundary] (root : V) : Real :=
  triangleFKGlobalConfigSum y0 y1 y2
      (fun sector => triHexFKTerminalWiredExternal q terminal boundary sector *
        triHexFKTerminalBoundaryReachObservable terminal boundary root sector) /
    triangleFKGlobalConfigSum y0 y1 y2
      (triHexFKTerminalWiredExternal q terminal boundary)


def starFKFiniteWiredBoundaryReachRatio
    {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype V] [DecidableEq V]
    (q y0 y1 y2 : Real) (terminal : ι → Fin 3 → V)
    (boundary : V → Prop) [DecidablePred boundary] (root : V) : Real :=
  starFKGlobalConfigSum q y0 y1 y2
      (fun sector => triHexFKTerminalWiredExternal q terminal boundary sector *
        triHexFKTerminalBoundaryReachObservable terminal boundary root sector) /
    starFKGlobalConfigSum q y0 y1 y2
      (triHexFKTerminalWiredExternal q terminal boundary)


end
end StatMech.FK.PeriodicPlanar
