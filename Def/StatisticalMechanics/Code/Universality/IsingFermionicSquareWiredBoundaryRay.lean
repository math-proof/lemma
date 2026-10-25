/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredBoundaryRay.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredBoundaryPhase


namespace StatMech.Universality

open Finset Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingDobrushinDomain

variable {P : PlanarZ2Subgraph} {M : Type*} [Fintype M] [DecidableEq M]


def signedExplorationMass (D : FKIsingDobrushinDomain P M)
    (e : M) (phase : Complex) : Real :=
  ∑ omega : ConfigSpace (Sym2 P.V),
    if e ∈ D.exploration omega then
      if D.windingPhase omega e = phase then D.criticalMass omega
      else -D.criticalMass omega
    else 0


end FKIsingDobrushinDomain
end
end StatMech.Universality
