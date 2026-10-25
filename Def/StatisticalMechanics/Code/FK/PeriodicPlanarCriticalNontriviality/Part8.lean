/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalNontriviality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarPercolationApproximation.Part3
import Theorem.StatisticalMechanics.Code.FK.PcNontrivial.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCriticalNontriviality.Part6
open MeasureTheory Set SimpleGraph Filter Topology
open scoped Classical BigOperators


namespace StatMech.FK.PeriodicPlanar

universe u

variable {V : Type u} [DecidableEq V]


def rootedOpenPathEvent
    (G : SimpleGraph V) [SimpleGraph.LocallyFinite G] (u : V) (n : Nat) :
    Set (ConfigSpace (Sym2 V)) :=
  ⋃ (c : RootedWalkCode G u n) (_ : (c.toWalk G).2.IsPath),
    walkOpenEvent (c.toWalk G).2

end StatMech.FK.PeriodicPlanar
