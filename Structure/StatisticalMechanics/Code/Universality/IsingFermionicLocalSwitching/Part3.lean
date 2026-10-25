/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalSwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDobrushin.Part8
import Theorem.StatisticalMechanics.Code.FK.FinitePatternEnergy.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLocalSwitching.Part6
open Finset Complex
open scoped BigOperators


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC

noncomputable section

namespace FKIsingDobrushinDomain

variable {P : PlanarZ2Subgraph} {M : Type*} [Fintype M] [DecidableEq M]

variable (D : FKIsingDobrushinDomain P M)

structure CaseOneExplorationSwitchingLaw where
  crossingA : P.V
  crossingB : P.V
  crossing_adj : P.G.Adj crossingA crossingB
  edges : Fin 4 -> M
  closed_not_mem : forall omega k,
    edges k ∉ D.exploration (setClosed s(crossingA, crossingB) omega)
  open_not_mem : forall omega k,
    edges k ∉ D.exploration (setOpen s(crossingA, crossingB) omega)

end FKIsingDobrushinDomain
end
end StatMech.Universality
