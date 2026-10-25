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
import Theorem.StatisticalMechanics.Code.FK.TriHexFKTorusSweep.Part3


namespace StatMech.FK.PeriodicPlanar

open Universality

open scoped BigOperators


noncomputable def connectedComponentEquivOfReachableIff
    {V : Type*} (G H : SimpleGraph V)
    (h : ∀ x y, G.Reachable x y ↔ H.Reachable x y) :
    G.ConnectedComponent ≃ H.ConnectedComponent where
  toFun := SimpleGraph.ConnectedComponent.lift
    (fun x => H.connectedComponentMk x) (by
      intro x y path _hpath
      exact SimpleGraph.ConnectedComponent.sound
        ((h x y).mp path.reachable))
  invFun := SimpleGraph.ConnectedComponent.lift
    (fun x => G.connectedComponentMk x) (by
      intro x y path _hpath
      exact SimpleGraph.ConnectedComponent.sound
        ((h x y).mpr path.reachable))
  left_inv component := by
    induction component using SimpleGraph.ConnectedComponent.ind with
    | h x => simp only [SimpleGraph.ConnectedComponent.lift_mk]
  right_inv component := by
    induction component using SimpleGraph.ConnectedComponent.ind with
    | h x => simp only [SimpleGraph.ConnectedComponent.lift_mk]


end StatMech.FK.PeriodicPlanar
