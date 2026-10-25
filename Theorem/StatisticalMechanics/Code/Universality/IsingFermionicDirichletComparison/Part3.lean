/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDirichletComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPrimitiveIntegration
import Def.StatisticalMechanics.Code.Universality.IsingFermionicDirichletComparison.Part3
open Finset SimpleGraph


namespace StatMech.Universality

noncomputable section

theorem isingFiniteGraphDirichletOperator_solve
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (boundary : V → Prop)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (rhs : V → ℝ) :
    isingFiniteGraphDirichletOperator G boundary
      (isingFiniteGraphDirichletSolve G boundary hhit rhs) = rhs :=
  Classical.choose_spec
    (LinearMap.injective_iff_surjective.mp
      (isingFiniteGraphDirichletOperator_injective G boundary hhit) rhs)


end
end StatMech.Universality
