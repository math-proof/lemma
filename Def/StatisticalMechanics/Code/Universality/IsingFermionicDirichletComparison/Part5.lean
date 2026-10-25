/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDirichletComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPrimitiveIntegration
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDirichletComparison.Part4
open Finset SimpleGraph


namespace StatMech.Universality

noncomputable section

noncomputable def isingFiniteGraphPoissonBarrierBound
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (boundary : V → Prop)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b) : ℝ :=
  (Finset.univ.image
    (isingFiniteGraphPoissonBarrier G boundary hhit)).max'
      (Finset.image_nonempty.mpr Finset.univ_nonempty)

end
end StatMech.Universality
