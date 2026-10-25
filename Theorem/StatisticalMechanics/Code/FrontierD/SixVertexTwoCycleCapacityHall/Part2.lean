/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexTwoCycleCapacityHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairedBranchResidualHall.Part3
import Structure.StatisticalMechanics.Code.FrontierD.SixVertexTwoCycleCapacityHall
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem FiniteKeyCapacityTransport.hall
    {Key : Type*} [Fintype Key] [DecidableEq Key]
    {sourceCapacity targetCapacity : Key -> Nat}
    {related : Key -> Key -> Prop} [DecidableRel related]
    (transport : FiniteKeyCapacityTransport Key
      sourceCapacity targetCapacity related) :
    forall sourceKeys : Finset Key,
      (∑ key ∈ sourceKeys, sourceCapacity key) <=
      ∑ key ∈ (Finset.univ.filter fun targetKey =>
          exists sourceKey, sourceKey ∈ sourceKeys ∧
            related sourceKey targetKey),
        targetCapacity key := by
  intro sourceKeys
  let targetKeys : Finset Key := Finset.univ.filter fun targetKey =>
    exists sourceKey, sourceKey ∈ sourceKeys ∧
      related sourceKey targetKey
  have houtside (target : Key) (htarget : target ∉ targetKeys) :
      ∑ source ∈ sourceKeys, transport.flow source target = 0 := by
    apply Finset.sum_eq_zero
    intro source hsource
    apply transport.supported
    intro hrelated
    apply htarget
    rw [show targetKeys = Finset.univ.filter fun targetKey =>
        exists sourceKey, sourceKey ∈ sourceKeys ∧
          related sourceKey targetKey by rfl]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨source, hsource, hrelated⟩
  calc
    (∑ key ∈ sourceKeys, sourceCapacity key) =
        ∑ source ∈ sourceKeys,
          ∑ target, transport.flow source target := by
      apply Finset.sum_congr rfl
      intro source hsource
      exact (transport.row_sum source).symm
    _ = ∑ target, ∑ source ∈ sourceKeys,
          transport.flow source target := by
      rw [Finset.sum_comm]
    _ = ∑ target ∈ targetKeys,
          ∑ source ∈ sourceKeys,
            transport.flow source target := by
      symm
      apply Finset.sum_subset (Finset.subset_univ targetKeys)
      intro target htargetUniv htargetOutside
      exact houtside target htargetOutside
    _ <= ∑ target ∈ targetKeys,
          ∑ source, transport.flow source target := by
      apply Finset.sum_le_sum
      intro target htarget
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ sourceKeys) (by
          intro source hsourceUniv hsourceOutside
          exact Nat.zero_le _)
    _ <= ∑ target ∈ targetKeys, targetCapacity target := by
      exact Finset.sum_le_sum fun target htarget =>
        transport.column_le target


theorem finiteKeyCapacityHall_of_injectiveRouting
    {Key : Type*} [Fintype Key] [DecidableEq Key]
    (sourceCapacity targetCapacity : Key -> Nat)
    (related : Key -> Key -> Prop) [DecidableRel related]
    (route : Key -> Key) (hinjective : Function.Injective route)
    (hsupported : forall key, related key (route key))
    (hcapacity : forall key,
      sourceCapacity key <= targetCapacity (route key)) :
    forall sourceKeys : Finset Key,
      (∑ key ∈ sourceKeys, sourceCapacity key) <=
        ∑ key ∈ (Finset.univ.filter fun targetKey =>
            exists sourceKey, sourceKey ∈ sourceKeys ∧
              related sourceKey targetKey),
          targetCapacity key := by
  intro sourceKeys
  let targetKeys : Finset Key := Finset.univ.filter fun targetKey =>
    exists sourceKey, sourceKey ∈ sourceKeys ∧ related sourceKey targetKey
  have himage : sourceKeys.image route ⊆ targetKeys := by
    intro target htarget
    obtain ⟨source, hsource, rfl⟩ := Finset.mem_image.mp htarget
    simp only [targetKeys, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨source, hsource, hsupported source⟩
  calc
    (∑ key ∈ sourceKeys, sourceCapacity key) <=
        ∑ key ∈ sourceKeys, targetCapacity (route key) := by
      exact Finset.sum_le_sum fun key _ => hcapacity key
    _ = ∑ key ∈ sourceKeys.image route, targetCapacity key := by
      rw [Finset.sum_image hinjective.injOn]
    _ <= ∑ key ∈ targetKeys, targetCapacity key := by
      exact Finset.sum_le_sum_of_subset_of_nonneg himage (by
        intro key _ _
        exact Nat.zero_le _)


end
end StatMech.FrontierD
