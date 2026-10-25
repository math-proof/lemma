/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitMultiplicityClass.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitExactTagSlotMove
open Finset


namespace StatMech.Ising

noncomputable section

noncomputable def lpReplicaEligibleInactivePairs
    {α β : Type*} [Fintype α] [DecidableEq α]
    (edge : α -> β) : Finset (Finset α) := by
  classical
  exact (Finset.univ.powersetCard 2).filter fun C =>
    Set.InjOn edge (↑(Finset.univ \ C) : Set α) ∧
      ∀ x ∈ C, ∀ y ∈ C, edge x = edge y


end
end StatMech.Ising
