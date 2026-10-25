/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWeightedDirichletComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDirichletComparison.Part5
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicWeightedDirichletComparison.Part4
open Finset SimpleGraph


namespace StatMech.Universality

noncomputable section

noncomputable def isingFiniteWeightedPoissonBarrierBound
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V → V → Real)
    (boundary : V → Prop)
    (hconductance : ∀ x y, 0 ≤ conductance x y)
    (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b) : Real :=
  (Finset.univ.image
    (isingFiniteWeightedPoissonBarrier G conductance boundary
      hconductance hpositive hhit)).max'
    (Finset.image_nonempty.mpr Finset.univ_nonempty)

end
end StatMech.Universality
