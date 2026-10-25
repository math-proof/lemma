/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalNontriviality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarPercolationApproximation.Part3
import Theorem.StatisticalMechanics.Code.FK.PcNontrivial.Part2
import Instance.StatisticalMechanics.Code.FK.PeriodicPlanarCriticalNontriviality
open MeasureTheory Set SimpleGraph Filter Topology
open scoped Classical BigOperators


namespace StatMech.FK.PeriodicPlanar

universe u

variable {V : Type u} [DecidableEq V]


def RootedWalkCode.toWalk
    (G : SimpleGraph V) [SimpleGraph.LocallyFinite G] {u : V} :
    {n : Nat} → RootedWalkCode G u n → Σ v, G.Walk u v
  | 0, _ => ⟨u, .nil⟩
  | n + 1, ⟨w, c⟩ =>
      let p := toWalk G c
      ⟨p.1, p.2.cons w.property⟩

end StatMech.FK.PeriodicPlanar
