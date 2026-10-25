/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWeightedDirichletComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDirichletComparison.Part5
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicWeightedDirichletComparison
open Finset SimpleGraph


namespace StatMech.Universality

noncomputable section

noncomputable def isingFiniteWeightedDirichletOperator
    {V : Type*} [Fintype V]
    (conductance : V → V → Real) (boundary : V → Prop) :
    (V → Real) →ₗ[Real] (V → Real) := by
  classical
  exact
    { toFun := fun f x ↦
        if boundary x then f x else
          isingFiniteWeightedLaplacian conductance f x
      map_add' := by
        intro f g
        funext x
        by_cases hx : boundary x
        · simp [hx]
        · simp only [if_neg hx, Pi.add_apply]
          exact isingFiniteWeightedLaplacian_add conductance f g x
      map_smul' := by
        intro c f
        funext x
        by_cases hx : boundary x
        · simp [hx]
        · simp only [if_neg hx, Pi.smul_apply, smul_eq_mul]
          exact isingFiniteWeightedLaplacian_const_mul conductance c f x }


end
end StatMech.Universality
