/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCaratheodoryApproximation.Part3
import Def.StatisticalMechanics.Code.Universality.IsingFermionicReflection.Part3
open Filter Metric Set Topology


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC

noncomputable section

namespace FKIsingCaratheodoryApproximation

variable (A : FKIsingCaratheodoryApproximation)


@[simp] theorem reflect_U : A.reflect.U = reflectComplexSet A.U := rfl

@[simp] theorem reflect_root :
    A.reflect.root = (starRingEnd Complex) A.root := rfl

@[simp] theorem reflect_carrier (n : Nat) :
    A.reflect.carrier n = reflectComplexSet (A.carrier n) := rfl

@[simp] theorem reflect_mesh (n : Nat) : A.reflect.mesh n = A.mesh n := rfl

@[simp] theorem reflect_medialEmbedding (n : Nat) (e : A.M n) :
    A.reflect.medialEmbedding n e =
      (starRingEnd Complex) (A.medialEmbedding n e) := rfl

@[simp] theorem reflect_rawInterpolant (n : Nat) (z : Complex) :
    A.reflect.rawInterpolant n z =
      A.rawInterpolant n ((starRingEnd Complex) z) := rfl

@[simp] theorem reflect_normalizedInterpolant (n : Nat) (z : Complex) :
    A.reflect.normalizedInterpolant n z =
      A.normalizedInterpolant n ((starRingEnd Complex) z) := rfl

end FKIsingCaratheodoryApproximation
end
end StatMech.Universality
