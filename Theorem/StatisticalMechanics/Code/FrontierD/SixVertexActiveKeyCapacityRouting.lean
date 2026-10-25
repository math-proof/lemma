/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexActiveKeyCapacityRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FiniteKeyCapacityMatching.Part3
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexActiveKeyCapacityRouting
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem finiteKeyCapacityHall_of_activeInjectiveRouting
    {Key : Type*} [Fintype Key] [DecidableEq Key]
    (sourceCapacity targetCapacity : Key -> Nat)
    (related : Key -> Key -> Prop) [DecidableRel related]
    (route : Key -> Key)
    (hinjective : forall first second,
      0 < sourceCapacity first -> 0 < sourceCapacity second ->
      route first = route second -> first = second)
    (hsupported : forall key, 0 < sourceCapacity key ->
      related key (route key))
    (hcapacity : forall key, 0 < sourceCapacity key ->
      sourceCapacity key <= targetCapacity (route key)) :
    forall sourceKeys : Finset Key,
      (∑ key ∈ sourceKeys, sourceCapacity key) <=
        ∑ key ∈ (Finset.univ.filter fun targetKey =>
            exists sourceKey, sourceKey ∈ sourceKeys /\
              related sourceKey targetKey),
          targetCapacity key := by
  intro sourceKeys
  let activeSourceKeys := sourceKeys.filter fun key =>
    0 < sourceCapacity key
  let targetKeys := Finset.univ.filter fun targetKey =>
    exists sourceKey, sourceKey ∈ sourceKeys /\ related sourceKey targetKey
  have hsourceSum :
      (∑ key ∈ sourceKeys, sourceCapacity key) =
        ∑ key ∈ activeSourceKeys, sourceCapacity key := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro key hsource hnotActive
    have hnotPos : ¬ 0 < sourceCapacity key := by
      intro hpos
      apply hnotActive
      exact Finset.mem_filter.mpr ⟨hsource, hpos⟩
    omega
  have hrouteInjective : Set.InjOn route activeSourceKeys := by
    intro first hfirst second hsecond heq
    apply hinjective first second
    · exact (Finset.mem_filter.mp hfirst).2
    · exact (Finset.mem_filter.mp hsecond).2
    · exact heq
  have himage : activeSourceKeys.image route ⊆ targetKeys := by
    intro target htarget
    obtain ⟨source, hsource, rfl⟩ := Finset.mem_image.mp htarget
    have hsourceOriginal : source ∈ sourceKeys :=
      (Finset.mem_filter.mp hsource).1
    have hsourcePos : 0 < sourceCapacity source :=
      (Finset.mem_filter.mp hsource).2
    simp only [targetKeys, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨source, hsourceOriginal, hsupported source hsourcePos⟩
  calc
    (∑ key ∈ sourceKeys, sourceCapacity key) =
        ∑ key ∈ activeSourceKeys, sourceCapacity key := hsourceSum
    _ <= ∑ key ∈ activeSourceKeys, targetCapacity (route key) := by
      apply Finset.sum_le_sum
      intro key hkey
      exact hcapacity key ((Finset.mem_filter.mp hkey).2)
    _ = ∑ key ∈ activeSourceKeys.image route, targetCapacity key := by
      rw [Finset.sum_image hrouteInjective]
    _ <= ∑ key ∈ targetKeys, targetCapacity key := by
      exact Finset.sum_le_sum_of_subset_of_nonneg himage (by
        intro key _ _
        exact Nat.zero_le _)

end
end StatMech.FrontierD
