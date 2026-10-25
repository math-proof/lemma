/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitProfileTransferGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedMatching.Part6
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitProfileTransferGraph.Part4


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaOffdiagDecoratedSource_card_eq_sum_transferComponents
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) =
      ∑ c ∈ lpReplicaOffdiagBalancedRelevantTransferComponents
          G sites i j q,
        (lpReplicaOffdiagDecoratedSourcesInTransferComponent
          G sites i j q c).card := by
  classical
  rw [← Finset.card_univ]
  simpa only [lpReplicaOffdiagDecoratedSourcesInTransferComponent] using
    Finset.card_eq_sum_card_fiberwise (by
      intro z hz
      unfold lpReplicaOffdiagBalancedRelevantTransferComponents
      exact Finset.mem_union.mpr (Or.inl
        (Finset.mem_image.mpr ⟨z, hz, rfl⟩)))

theorem lpReplicaOffdiagBalancedOutputs_card_eq_sum_transferComponents
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    (lpReplicaOffdiagBalancedOutputs G sites i j q).card =
      ∑ c ∈ lpReplicaOffdiagBalancedRelevantTransferComponents
          G sites i j q,
        (lpReplicaOffdiagBalancedOutputsInTransferComponent
          G sites i j q c).card := by
  classical
  simpa only [lpReplicaOffdiagBalancedOutputsInTransferComponent] using
    Finset.card_eq_sum_card_fiberwise (by
      intro y hy
      unfold lpReplicaOffdiagBalancedRelevantTransferComponents
      exact Finset.mem_union.mpr (Or.inr
        (Finset.mem_image.mpr ⟨y, hy, rfl⟩)))


theorem lpReplicaOffdiagOrbitAtomCardInequality_of_transferComponentCards
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : ∀ c ∈ lpReplicaOffdiagBalancedRelevantTransferComponents
        G sites i j q,
      (lpReplicaOffdiagDecoratedSourcesInTransferComponent
          G sites i j q c).card <=
        (lpReplicaOffdiagBalancedOutputsInTransferComponent
          G sites i j q c).card) :
    LPReplicaOffdiagOrbitAtomCardInequality G sites i j q := by
  apply lpReplicaOffdiagOrbitAtomCardInequality_of_balancedOutputCard
  rw [lpReplicaOffdiagDecoratedSource_card_eq_sum_transferComponents,
    lpReplicaOffdiagBalancedOutputs_card_eq_sum_transferComponents]
  exact Finset.sum_le_sum hcard

end
end StatMech.Ising
