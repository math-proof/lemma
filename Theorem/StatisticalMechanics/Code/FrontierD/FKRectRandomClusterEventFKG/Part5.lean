/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterEventFKG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutPushforward.Part9
import Def.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterEventFKG.Part4


namespace StatMech.FrontierD

noncomputable section

theorem fkRectCriticalEventMass_finiteUnion_le_sum
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    {ι : Type*} (s : Finset ι) (A : ι → Set R.Configuration) :
    fkRectCriticalEventMass R q (fkRectFiniteEventUnion s A) ≤
      ∑ i ∈ s, fkRectCriticalEventMass R q (A i) := by
  classical
  unfold fkRectCriticalEventMass
  have hpoint (omega : R.Configuration) :
      (fkRectFiniteEventUnion s A).indicator
          (fun omega => fkRectCriticalRandomClusterProb R q omega) omega ≤
        ∑ i ∈ s, (A i).indicator
          (fun omega => fkRectCriticalRandomClusterProb R q omega) omega := by
    by_cases hU : omega ∈ fkRectFiniteEventUnion s A
    · have hU' := hU
      obtain ⟨i, hi, hAi⟩ := hU
      rw [Set.indicator_of_mem hU']
      have hle := Finset.single_le_sum
        (s := s)
        (f := fun j => (A j).indicator
          (fun eta => fkRectCriticalRandomClusterProb R q eta) omega)
        (fun j hj => Set.indicator_nonneg
          (fun _ _ => fkRectCriticalRandomClusterProb_nonneg R hq _) _)
        hi
      simpa [Set.indicator_of_mem hAi] using hle
    · rw [Set.indicator_of_notMem hU]
      exact Finset.sum_nonneg fun i _ => Set.indicator_nonneg
        (fun _ _ => fkRectCriticalRandomClusterProb_nonneg R hq _) _
  calc
    (∑ omega : R.Configuration,
      (fkRectFiniteEventUnion s A).indicator
        (fun omega => fkRectCriticalRandomClusterProb R q omega) omega) ≤
        ∑ omega : R.Configuration, ∑ i ∈ s,
          (A i).indicator
            (fun omega => fkRectCriticalRandomClusterProb R q omega) omega :=
      Finset.sum_le_sum fun omega _ => hpoint omega
    _ = ∑ i ∈ s, ∑ omega : R.Configuration,
          (A i).indicator
            (fun omega => fkRectCriticalRandomClusterProb R q omega) omega := by
      rw [Finset.sum_comm]


theorem fkRectCriticalEventMass_union_le_add
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (A B : Set R.Configuration) :
    fkRectCriticalEventMass R q (A ∪ B) ≤
      fkRectCriticalEventMass R q A + fkRectCriticalEventMass R q B := by
  let E : Bool → Set R.Configuration := fun b => if b then A else B
  have hset : A ∪ B = fkRectFiniteEventUnion Finset.univ E := by
    ext omega
    constructor
    · rintro (hA | hB)
      · exact ⟨true, Finset.mem_univ _, by simpa [E] using hA⟩
      · exact ⟨false, Finset.mem_univ _, by simpa [E] using hB⟩
    · rintro ⟨b, _, hb⟩
      cases b
      · exact Or.inr (by simpa [E] using hb)
      · exact Or.inl (by simpa [E] using hb)
  rw [hset]
  have h := fkRectCriticalEventMass_finiteUnion_le_sum
    R hq Finset.univ E
  simpa [E, add_comm] using h


theorem exists_card_mul_eventMass_ge_of_finiteUnion_ge
    (R : FKRectTorus) {q c : Real} (hq : 0 < q)
    {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    (A : ι → Set R.Configuration)
    (hc : c ≤ fkRectCriticalEventMass R q
      (fkRectFiniteEventUnion s A)) :
    ∃ i ∈ s, c ≤ (s.card : Real) * fkRectCriticalEventMass R q (A i) := by
  classical
  have hsum := hc.trans
    (fkRectCriticalEventMass_finiteUnion_le_sum R hq s A)
  by_contra hex
  have hex' : ∀ i ∈ s,
      (s.card : Real) * fkRectCriticalEventMass R q (A i) < c := by
    intro i hi
    exact lt_of_not_ge (fun h => hex ⟨i, hi, h⟩)
  have hcardPos : (0 : Real) < s.card := by
    exact_mod_cast Finset.card_pos.mpr hs
  have hstrict :
      ∑ i ∈ s, (s.card : Real) * fkRectCriticalEventMass R q (A i) <
        ∑ i ∈ s, c :=
    Finset.sum_lt_sum_of_nonempty hs (fun i hi => hex' i hi)
  rw [← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul] at hstrict
  nlinarith

end
end StatMech.FrontierD
