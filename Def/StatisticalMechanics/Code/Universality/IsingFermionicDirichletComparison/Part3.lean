/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDirichletComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPrimitiveIntegration
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDirichletComparison.Part2
open Finset SimpleGraph


namespace StatMech.Universality

noncomputable section

noncomputable def isingFiniteGraphDirichletSolve
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (boundary : V → Prop)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (rhs : V → ℝ) : V → ℝ :=
  Classical.choose
    (LinearMap.injective_iff_surjective.mp
      (isingFiniteGraphDirichletOperator_injective G boundary hhit) rhs)

end
end StatMech.Universality
