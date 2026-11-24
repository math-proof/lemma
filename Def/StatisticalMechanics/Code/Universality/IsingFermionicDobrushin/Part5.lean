module
public import Theorem.StatisticalMechanics.Code.Universality.IsingSHolo.Part7
public import Theorem.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part6
public import Theorem.StatisticalMechanics.Code.BeffaraDC.SelfDualValue
public import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDobrushin.Part3
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


def fermionicSummand (omega : ConfigSpace (Sym2 P.V)) (e : M) : Complex :=
  if e ∈ D.exploration omega then
    (D.criticalMass omega : Complex) * D.windingPhase omega e
  else 0


def fermionicObservable (e : M) : Complex :=
  ∑ omega : ConfigSpace (Sym2 P.V), D.fermionicSummand omega e


def explorationMass (e : M) : Real :=
  ∑ omega : ConfigSpace (Sym2 P.V),
    if e ∈ D.exploration omega then D.criticalMass omega else 0

end FKIsingDobrushinDomain
end
end StatMech.Universality
