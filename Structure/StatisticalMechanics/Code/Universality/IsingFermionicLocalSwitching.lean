/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalSwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDobrushin.Part8
import Theorem.StatisticalMechanics.Code.FK.FinitePatternEnergy.Part3
import Def.StatisticalMechanics.Code.Universality.IsingFermionicLocalSwitching.Part3
open Finset Complex
open scoped BigOperators


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC

noncomputable section

namespace FKIsingDobrushinDomain

variable {P : PlanarZ2Subgraph} {M : Type*} [Fintype M] [DecidableEq M]

variable (D : FKIsingDobrushinDomain P M)

structure CaseTwoExplorationSwitchingLaw where
  crossingA : P.V
  crossingB : P.V
  crossing_adj : P.G.Adj crossingA crossingB
  edges : Fin 4 -> M
  closed_endpoints_not_reachable : forall omega,
    ¬(openSub P.G (setClosed s(crossingA, crossingB) omega) ⊔ D.wiring).Reachable
      crossingA crossingB
  closed_mem_zero : forall omega,
    edges 0 ∈ D.exploration (setClosed s(crossingA, crossingB) omega)
  closed_not_mem_one : forall omega,
    edges 1 ∉ D.exploration (setClosed s(crossingA, crossingB) omega)
  closed_mem_two : forall omega,
    edges 2 ∈ D.exploration (setClosed s(crossingA, crossingB) omega)
  closed_not_mem_three : forall omega,
    edges 3 ∉ D.exploration (setClosed s(crossingA, crossingB) omega)
  open_mem : forall omega k,
    edges k ∈ D.exploration (setOpen s(crossingA, crossingB) omega)
  paired_balance : D.ClosedOpenPairedBalance s(crossingA, crossingB) edges

end FKIsingDobrushinDomain
end
end StatMech.Universality
