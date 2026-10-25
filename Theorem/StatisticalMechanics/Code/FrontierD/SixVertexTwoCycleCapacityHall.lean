/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexTwoCycleCapacityHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairedBranchResidualHall.Part3
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexTwoCycleCapacityHall
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem finiteRelationHall_of_keyCapacity
    {Source Target Key : Type*}
    [Fintype Source] [Fintype Target] [Fintype Key]
    [DecidableEq Source] [DecidableEq Target] [DecidableEq Key]
    (sourceKey : Source -> Key) (targetKey : Target -> Key)
    (keyRelated : Key -> Key -> Prop) [DecidableRel keyRelated]
    (related : Source -> Target -> Prop) [DecidableRel related]
    (hsound : forall source target,
      keyRelated (sourceKey source) (targetKey target) ->
        related source target)
    (hcapacity : forall sourceKeys : Finset Key,
      (∑ key ∈ sourceKeys,
        Fintype.card {source : Source // sourceKey source = key}) <=
      ∑ key ∈ (Finset.univ.filter fun targetKeyValue =>
          exists sourceKeyValue,
            sourceKeyValue ∈ sourceKeys ∧
              keyRelated sourceKeyValue targetKeyValue),
        Fintype.card {target : Target // targetKey target = key}) :
    forall sources : Finset Source,
      sources.card <=
        (Finset.univ.filter fun target => exists source,
          source ∈ sources ∧ related source target).card := by
  intro sources
  let sourceKeys : Finset Key := sources.image sourceKey
  let targetKeys : Finset Key := Finset.univ.filter fun targetKeyValue =>
    exists sourceKeyValue,
      sourceKeyValue ∈ sourceKeys ∧
        keyRelated sourceKeyValue targetKeyValue
  let keyTargets : Finset Target := Finset.univ.filter fun target =>
    targetKey target ∈ targetKeys
  let relationTargets : Finset Target := Finset.univ.filter fun target =>
    exists source, source ∈ sources ∧ related source target
  have hsource : sources.card <=
      ∑ key ∈ sourceKeys,
        Fintype.card {source : Source // sourceKey source = key} := by
    rw [Finset.card_eq_sum_card_image sourceKey sources]
    apply Finset.sum_le_sum
    intro key hkey
    calc
      (sources.filter fun source => sourceKey source = key).card <=
          (Finset.univ.filter fun source =>
            sourceKey source = key).card := by
        apply Finset.card_le_card
        exact Finset.filter_subset_filter _ (Finset.subset_univ sources)
      _ = Fintype.card {source : Source // sourceKey source = key} := by
        rw [Fintype.card_subtype]
  have hkeyTargets :
      (∑ key ∈ targetKeys,
        Fintype.card {target : Target // targetKey target = key}) =
        keyTargets.card := by
    rw [show keyTargets = Finset.univ.filter fun target =>
        targetKey target ∈ targetKeys by rfl]
    simp only [Fintype.card_subtype]
    exact Finset.sum_card_fiberwise_eq_card_filter
      Finset.univ targetKeys targetKey
  have hsubset : keyTargets ⊆ relationTargets := by
    intro target htarget
    have htargetKey : targetKey target ∈ targetKeys := by
      simpa [keyTargets] using htarget
    obtain ⟨sourceKeyValue, hsourceKey, hkeyRelated⟩ := by
      simpa [targetKeys] using htargetKey
    obtain ⟨source, hsource, hsourceKeyEq⟩ :=
      Finset.mem_image.mp hsourceKey
    have hrelated : related source target := by
      apply hsound source target
      rwa [hsourceKeyEq]
    rw [show relationTargets = Finset.univ.filter fun target =>
        exists source, source ∈ sources ∧ related source target by rfl]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨source, hsource, hrelated⟩
  calc
    sources.card <=
        ∑ key ∈ sourceKeys,
          Fintype.card {source : Source // sourceKey source = key} := hsource
    _ <= ∑ key ∈ targetKeys,
          Fintype.card {target : Target // targetKey target = key} := by
      exact hcapacity sourceKeys
    _ = keyTargets.card := hkeyTargets
    _ <= relationTargets.card := Finset.card_le_card hsubset


end
end StatMech.FrontierD
