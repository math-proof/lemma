/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCaratheodoryApproximation.Part3
import Def.StatisticalMechanics.Code.Universality.IsingFermionicReflection.Part2
open Filter Metric Set Topology


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC

noncomputable section

@[simp] theorem FKIsingDobrushinDomain.reflect_medialPosition
    {P : PlanarZ2Subgraph} {M : Type*} [Fintype M] [DecidableEq M]
    (D : FKIsingDobrushinDomain P M) (e : M) :
    D.reflect.medialPosition e =
      (starRingEnd Complex) (D.medialPosition e) := rfl

@[simp] theorem FKIsingDobrushinDomain.reflect_fermionicObservable
    {P : PlanarZ2Subgraph} {M : Type*} [Fintype M] [DecidableEq M]
    (D : FKIsingDobrushinDomain P M) (e : M) :
    D.reflect.fermionicObservable e = D.fermionicObservable e := rfl

@[simp] theorem FKIsingDobrushinDomain.reflect_normalizedFermionicObservable
    {P : PlanarZ2Subgraph} {M : Type*} [Fintype M] [DecidableEq M]
    (D : FKIsingDobrushinDomain P M) (mesh : Real) (e : M) :
    D.reflect.normalizedFermionicObservable mesh e =
      D.normalizedFermionicObservable mesh e := rfl

end
end StatMech.Universality
