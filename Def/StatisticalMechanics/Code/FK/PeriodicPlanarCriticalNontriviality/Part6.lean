/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalNontriviality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarPercolationApproximation.Part3
import Theorem.StatisticalMechanics.Code.FK.PcNontrivial.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCriticalNontriviality.Part4
open MeasureTheory Set SimpleGraph Filter Topology
open scoped Classical BigOperators


namespace StatMech.FK.PeriodicPlanar

universe u

variable {V : Type u} [DecidableEq V]


noncomputable def rootedReachableFinset
    (G : SimpleGraph V) [SimpleGraph.LocallyFinite G]
    (u : V) (n : Nat) : Finset V :=
  (Finset.univ : Finset (Σ k : Fin n, RootedWalkCode G u k)).image
    (fun kc => (kc.2.toWalk G).1)

end StatMech.FK.PeriodicPlanar
