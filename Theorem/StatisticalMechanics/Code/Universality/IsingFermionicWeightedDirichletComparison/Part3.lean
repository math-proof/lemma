/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWeightedDirichletComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDirichletComparison.Part5
import Def.StatisticalMechanics.Code.Universality.IsingFermionicWeightedDirichletComparison.Part3
open Finset SimpleGraph


namespace StatMech.Universality

noncomputable section

theorem isingFiniteWeightedDirichletOperator_solve
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V → V → Real)
    (boundary : V → Prop)
    (hconductance : ∀ x y, 0 ≤ conductance x y)
    (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (rhs : V → Real) :
    isingFiniteWeightedDirichletOperator conductance boundary
      (isingFiniteWeightedDirichletSolve G conductance boundary
        hconductance hpositive hhit rhs) = rhs :=
  Classical.choose_spec
    (LinearMap.injective_iff_surjective.mp
      (isingFiniteWeightedDirichletOperator_injective
        G conductance boundary hconductance hpositive hhit) rhs)


end
end StatMech.Universality
