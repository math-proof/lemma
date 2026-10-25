/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalNontriviality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarPercolationApproximation.Part3
import Theorem.StatisticalMechanics.Code.FK.PcNontrivial.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCriticalNontriviality.Part2
open MeasureTheory Set SimpleGraph Filter Topology
open scoped Classical BigOperators


namespace StatMech.FK.PeriodicPlanar

universe u

variable {V : Type u} [DecidableEq V]


def RootedWalkCode (G : SimpleGraph V) [SimpleGraph.LocallyFinite G]
    (u : V) : Nat → Type u
  | 0 => ULift.{u} PUnit
  | n + 1 => Σ w : G.neighborSet u, RootedWalkCode G w n

end StatMech.FK.PeriodicPlanar
