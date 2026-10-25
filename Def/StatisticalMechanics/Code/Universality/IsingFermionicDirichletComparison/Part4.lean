/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDirichletComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPrimitiveIntegration
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDirichletComparison.Part3
open Finset SimpleGraph


namespace StatMech.Universality

noncomputable section

noncomputable def isingFiniteGraphPoissonBarrier
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (boundary : V → Prop)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b) : V → ℝ := by
  classical
  exact isingFiniteGraphDirichletSolve G boundary hhit
    (fun x ↦ if boundary x then 0 else -1)

end
end StatMech.Universality
