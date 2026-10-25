/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalNontriviality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarPercolationApproximation.Part3
import Theorem.StatisticalMechanics.Code.FK.PcNontrivial.Part2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarCriticalNontriviality.Part3
open MeasureTheory Set SimpleGraph Filter Topology
open scoped Classical BigOperators


namespace StatMech.FK.PeriodicPlanar

universe u

variable {V : Type u} [DecidableEq V]


noncomputable instance instFintypeRootedWalkCode
    (G : SimpleGraph V) [SimpleGraph.LocallyFinite G] (u : V) (n : Nat) :
    Fintype (RootedWalkCode G u n) := by
  induction n generalizing u with
  | zero => exact Fintype.ofEquiv PUnit Equiv.ulift.symm
  | succ n ih =>
      dsimp only [RootedWalkCode]
      letI (w : G.neighborSet u) : Fintype (RootedWalkCode G w n) := ih w
      infer_instance


end StatMech.FK.PeriodicPlanar
