/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDirichletComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPrimitiveIntegration
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDirichletComparison
open Finset SimpleGraph


namespace StatMech.Universality

noncomputable section

noncomputable def isingFiniteGraphDirichletOperator
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (boundary : V → Prop) :
    (V → ℝ) →ₗ[ℝ] (V → ℝ) := by
  classical
  exact
    { toFun := fun f x ↦
        if boundary x then f x else isingFiniteGraphLaplacian G f x
      map_add' := by
        intro f g
        funext x
        by_cases hx : boundary x
        · simp [hx]
        · simp only [if_neg hx, Pi.add_apply]
          exact isingFiniteGraphLaplacian_add G f g x
      map_smul' := by
        intro c f
        funext x
        by_cases hx : boundary x
        · simp [hx]
        · simp only [if_neg hx, Pi.smul_apply, smul_eq_mul]
          exact isingFiniteGraphLaplacian_const_mul G c f x }


end
end StatMech.Universality
