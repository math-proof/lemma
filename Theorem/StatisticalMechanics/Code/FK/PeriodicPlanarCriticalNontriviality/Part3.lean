/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalNontriviality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarPercolationApproximation.Part3
import Theorem.StatisticalMechanics.Code.FK.PcNontrivial.Part2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarCriticalNontriviality.Part4
open MeasureTheory Set SimpleGraph Filter Topology
open scoped Classical BigOperators


namespace StatMech.FK.PeriodicPlanar

universe u

variable {V : Type u} [DecidableEq V]


@[simp] theorem RootedWalkCode.length_toWalk
    (G : SimpleGraph V) [SimpleGraph.LocallyFinite G]
    {u : V} {n : Nat} (c : RootedWalkCode G u n) :
    (c.toWalk G).2.length = n := by
  induction n generalizing u with
  | zero => cases c; rfl
  | succ n ih =>
      rcases c with ⟨w, c⟩
      simp only [RootedWalkCode.toWalk, Walk.length_cons, ih]


end StatMech.FK.PeriodicPlanar
