/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalNontriviality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarPercolationApproximation.Part3
import Theorem.StatisticalMechanics.Code.FK.PcNontrivial.Part2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarCriticalNontriviality.Part6
open MeasureTheory Set SimpleGraph Filter Topology
open scoped Classical BigOperators


namespace StatMech.FK.PeriodicPlanar

universe u

variable {V : Type u} [DecidableEq V]


theorem endpoint_mem_rootedReachableFinset
    (G : SimpleGraph V) [SimpleGraph.LocallyFinite G]
    {u v : V} (p : G.Walk u v) {n : Nat} (hp : p.length < n) :
    v ∈ rootedReachableFinset G u n := by
  rw [rootedReachableFinset, Finset.mem_image]
  refine ⟨⟨⟨p.length, hp⟩, RootedWalkCode.ofWalk G p⟩, Finset.mem_univ _, ?_⟩
  exact RootedWalkCode.toWalk_ofWalk_endpoint G p


end StatMech.FK.PeriodicPlanar
