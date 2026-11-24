module
public import Theorem.StatisticalMechanics.Code.Universality.IsingSHolo.Part7
public import Theorem.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part6
public import Theorem.StatisticalMechanics.Code.BeffaraDC.SelfDualValue
public import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
public import Instance.StatisticalMechanics.Code.Universality.IsingFermionicDobrushin
open Finset Complex
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDobrushin.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC

noncomputable section

variable (P : PlanarZ2Subgraph) (M : Type*) [Fintype M] [DecidableEq M]


namespace FKIsingDobrushinDomain

variable {P M} (D : FKIsingDobrushinDomain P M)


def criticalMass (omega : ConfigSpace (Sym2 P.V)) : Real :=
  bcProb P.G D.wiring fkIsingCriticalParameter 2 omega

end FKIsingDobrushinDomain
end
end StatMech.Universality
