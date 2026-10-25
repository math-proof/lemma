/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTightFamilyCutParity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyRootCollision
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalCollisionSquare
import Abbrev.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyCutParity
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


set_option maxHeartbeats 1000000 in


theorem canonicalOpposingRootCutsAtRight_crossTranslatedRows
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (c d : leftMaskFiber ends m j k l zero p)
    (q : rightMaskFiber ends m j k l zero p)
    (hcuts : CanonicalOpposingRootCutsAtRight
      ends m j k l zero p c d q) :
    ∃ a b : leftMaskFiber ends m j k l zero p,
      canonicalCollisionOppositeRow m q.1.1 c.1.1 d.1.1 =
          canonicalTranslatedRow ends m k zero b.1.1 c.1.1 ∧
      canonicalCollisionOppositeRow m q.1.1 c.1.1 d.1.1 =
          canonicalTranslatedRow ends m k zero a.1.1 d.1.1 ∧
      CanonicalTranslatedRowRootComponentCut
          ends m k zero b.1.1 c.1.1 ∧
      CanonicalTranslatedRowRootComponentCut
          ends m k zero a.1.1 d.1.1 := by
  obtain ⟨a, b, hac, hbd, hqa, hqb, -, -, hcutbc, hcutad⟩ := hcuts
  have hqrowa : rowClass m q.1.1 0 =
      canonicalTranslatedRow ends m k zero a.1.1 c.1.1 := by
    rw [hqa]
    have hv := canonicalTransfers_valid_on_sameMask hloop hjk hkl a c
    rw [rowClass_balancedSwap_zero hv.1 hv.2.1]
    rfl
  have hqrowb : rowClass m q.1.1 0 =
      canonicalTranslatedRow ends m k zero b.1.1 d.1.1 := by
    rw [hqb]
    have hv := canonicalTransfers_valid_on_sameMask hloop hjk hkl b d
    rw [rowClass_balancedSwap_zero hv.1 hv.2.1]
    rfl
  have htrans : canonicalTranslatedRow ends m k zero a.1.1 c.1.1 =
      canonicalTranslatedRow ends m k zero b.1.1 d.1.1 :=
    hqrowa.symm.trans hqrowb
  have hopp := canonicalTranslatedRow_opposite_eq_of_eq
    ends m k zero a.1.1 b.1.1 c.1.1 d.1.1 htrans
  have hexp : canonicalTranslatedRow ends m k zero b.1.1 c.1.1 =
      canonicalCollisionOppositeRow m q.1.1 c.1.1 d.1.1 := by
    rw [hopp, canonicalCollisionOppositeRow, hqrowa]
    unfold canonicalTranslatedRow
    calc
      rowClass m d.1.1 0 ∆ canonicalTransferUnion ends m k zero a.1.1 =
          canonicalTransferUnion ends m k zero a.1.1 ∆
            rowClass m d.1.1 0 := symmDiff_comm _ _
      _ = (rowClass m c.1.1 0 ∆ rowClass m c.1.1 0) ∆
            canonicalTransferUnion ends m k zero a.1.1 ∆
              rowClass m d.1.1 0 := by
        rw [symmDiff_self, bot_symmDiff]
      _ = (rowClass m c.1.1 0 ∆
            canonicalTransferUnion ends m k zero a.1.1) ∆
          rowClass m c.1.1 0 ∆ rowClass m d.1.1 0 := by ac_rfl
  exact ⟨a, b, hexp.symm, hexp.symm.trans hopp, hcutbc, hcutad⟩

set_option maxHeartbeats 1000000 in


theorem canonicalCommonImage_opposingAtRight_or_twoCommon
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (c d : leftMaskFiber ends m j k l zero p) (hcd : c ≠ d)
    (q : rightMaskFiber ends m j k l zero p)
    (hqc : q ∈ canonicalMaskRightImages ends m j k l zero p c)
    (hqd : q ∈ canonicalMaskRightImages ends m j k l zero p d) :
    CanonicalOpposingRootCutsAtRight
        ends m j k l zero p c d q ∨
      CanonicalTightTwoRowCollision ends m j k l zero p c d := by
  obtain ⟨a, hac, hqa⟩ := (mem_canonicalMaskRightImages_iff
    ends m j k l zero p c q).mp hqc
  obtain ⟨b, hbd, hqb⟩ := (mem_canonicalMaskRightImages_iff
    ends m j k l zero p d q).mp hqd
  have hqrowa : rowClass m q.1.1 0 =
      canonicalTranslatedRow ends m k zero a.1.1 c.1.1 := by
    rw [hqa]
    have hv := canonicalTransfers_valid_on_sameMask hloop hjk hkl a c
    rw [rowClass_balancedSwap_zero hv.1 hv.2.1]
    rfl
  have hqrowb : rowClass m q.1.1 0 =
      canonicalTranslatedRow ends m k zero b.1.1 d.1.1 := by
    rw [hqb]
    have hv := canonicalTransfers_valid_on_sameMask hloop hjk hkl b d
    rw [rowClass_balancedSwap_zero hv.1 hv.2.1]
    rfl
  have htrans : canonicalTranslatedRow ends m k zero a.1.1 c.1.1 =
      canonicalTranslatedRow ends m k zero b.1.1 d.1.1 :=
    hqrowa.symm.trans hqrowb
  have hopp := canonicalTransferWorks_opposite_iff_of_translatedRow_eq
    hloop hjk hkl a b c d htrans
  by_cases hbc : CanonicalTransferWorks ends m k zero b.1.1 c.1.1
  · exact Or.inr
      (exists_two_common_canonicalMaskRightImages_of_collisionSquare
        hloop hjk hkl a b c d hcd hac htrans hbc)
  · have had : ¬ CanonicalTransferWorks
        ends m k zero a.1.1 d.1.1 := fun had => hbc (hopp.mpr had)
    exact Or.inl ⟨a, b, hac, hbd, hqa, hqb, hbc, had,
      canonicalTransferWorks_failed_rootComponentCut
        hloop hjk hkl b c hbc,
      canonicalTransferWorks_failed_rootComponentCut
        hloop hjk hkl a d had⟩

set_option maxHeartbeats 1000000 in


theorem canonicalSelfImage_owner_rootComponentCut_or_works_twoCommon
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    {p : Finset I × Finset I}
    (c d : leftMaskFiber ends m j k l zero p) (hcd : c ≠ d)
    (howner : canonicalTransferMapOfWorks
        ends m j k l zero hloop hjk hkl p c c
          (canonicalTransferWorks_self hloop hjk hkl hk0 c) ∈
      canonicalMaskRightImages ends m j k l zero p d) :
    CanonicalTranslatedRowRootComponentCut
        ends m k zero c.1.1 d.1.1 ∨
      (CanonicalTransferWorks ends m k zero c.1.1 d.1.1 ∧
        CanonicalTightTwoRowCollision ends m j k l zero p c d) := by
  let q := canonicalTransferMapOfWorks
    ends m j k l zero hloop hjk hkl p c c
      (canonicalTransferWorks_self hloop hjk hkl hk0 c)
  obtain ⟨b, hbd, hqb⟩ := (mem_canonicalMaskRightImages_iff
    ends m j k l zero p d q).mp howner
  have hqrowc : rowClass m q.1.1 0 =
      canonicalTranslatedRow ends m k zero c.1.1 c.1.1 :=
    rowClass_zero_canonicalTransferMapOfWorks
      ends m j k l zero hloop hjk hkl p c c
        (canonicalTransferWorks_self hloop hjk hkl hk0 c)
  have hqrowb : rowClass m q.1.1 0 =
      canonicalTranslatedRow ends m k zero b.1.1 d.1.1 := by
    rw [hqb]
    have hv := canonicalTransfers_valid_on_sameMask hloop hjk hkl b d
    rw [rowClass_balancedSwap_zero hv.1 hv.2.1]
    rfl
  have htrans : canonicalTranslatedRow ends m k zero c.1.1 c.1.1 =
      canonicalTranslatedRow ends m k zero b.1.1 d.1.1 :=
    hqrowc.symm.trans hqrowb
  have hopp := canonicalTransferWorks_opposite_iff_of_translatedRow_eq
    hloop hjk hkl c b c d htrans
  by_cases hbc : CanonicalTransferWorks ends m k zero b.1.1 c.1.1
  · exact Or.inr ⟨hopp.mp hbc,
      exists_two_common_canonicalMaskRightImages_of_collisionSquare
        hloop hjk hkl c b c d hcd
          (canonicalTransferWorks_self hloop hjk hkl hk0 c)
          htrans hbc⟩
  · have hcdBad : ¬ CanonicalTransferWorks
        ends m k zero c.1.1 d.1.1 := fun hcdWorks =>
      hbc (hopp.mpr hcdWorks)
    exact Or.inl (canonicalTransferWorks_failed_rootComponentCut
      hloop hjk hkl c d hcdBad)


theorem canonicalSelfImage_owner_rootComponentCut_or_twoCommon
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    {p : Finset I × Finset I}
    (c d : leftMaskFiber ends m j k l zero p) (hcd : c ≠ d)
    (howner : canonicalTransferMapOfWorks
        ends m j k l zero hloop hjk hkl p c c
          (canonicalTransferWorks_self hloop hjk hkl hk0 c) ∈
      canonicalMaskRightImages ends m j k l zero p d) :
    CanonicalTranslatedRowRootComponentCut
        ends m k zero c.1.1 d.1.1 ∨
      CanonicalTightTwoRowCollision ends m j k l zero p c d := by
  rcases canonicalSelfImage_owner_rootComponentCut_or_works_twoCommon
      hloop hjk hkl hk0 c d hcd howner with hcut | ⟨-, hsquare⟩
  · exact Or.inl hcut
  · exact Or.inr hsquare

set_option maxHeartbeats 1000000 in


theorem canonicalReferenceImage_owner_rootComponentCut_or_works_twoCommon
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (r c d : leftMaskFiber ends m j k l zero p)
    (hrc : CanonicalTransferWorks ends m k zero r.1.1 c.1.1)
    (hcd : c ≠ d)
    (howner : canonicalTransferMapOfWorks
        ends m j k l zero hloop hjk hkl p r c hrc ∈
      canonicalMaskRightImages ends m j k l zero p d) :
    CanonicalTranslatedRowRootComponentCut
        ends m k zero r.1.1 d.1.1 ∨
      (CanonicalTransferWorks ends m k zero r.1.1 d.1.1 ∧
        CanonicalTightTwoRowCollision ends m j k l zero p c d) := by
  let q := canonicalTransferMapOfWorks
    ends m j k l zero hloop hjk hkl p r c hrc
  obtain ⟨b, hbd, hqb⟩ := (mem_canonicalMaskRightImages_iff
    ends m j k l zero p d q).mp howner
  have hqrowr : rowClass m q.1.1 0 =
      canonicalTranslatedRow ends m k zero r.1.1 c.1.1 :=
    rowClass_zero_canonicalTransferMapOfWorks
      ends m j k l zero hloop hjk hkl p r c hrc
  have hqrowb : rowClass m q.1.1 0 =
      canonicalTranslatedRow ends m k zero b.1.1 d.1.1 := by
    rw [hqb]
    have hv := canonicalTransfers_valid_on_sameMask hloop hjk hkl b d
    rw [rowClass_balancedSwap_zero hv.1 hv.2.1]
    rfl
  have htrans : canonicalTranslatedRow ends m k zero r.1.1 c.1.1 =
      canonicalTranslatedRow ends m k zero b.1.1 d.1.1 :=
    hqrowr.symm.trans hqrowb
  have hopp := canonicalTransferWorks_opposite_iff_of_translatedRow_eq
    hloop hjk hkl r b c d htrans
  by_cases hbc : CanonicalTransferWorks ends m k zero b.1.1 c.1.1
  · exact Or.inr ⟨hopp.mp hbc,
      exists_two_common_canonicalMaskRightImages_of_collisionSquare
        hloop hjk hkl r b c d hcd hrc htrans hbc⟩
  · have hrdBad : ¬ CanonicalTransferWorks
        ends m k zero r.1.1 d.1.1 := fun hrd => hbc (hopp.mpr hrd)
    exact Or.inl (canonicalTransferWorks_failed_rootComponentCut
      hloop hjk hkl r d hrdBad)


theorem tightFamily_referenceImage_internalCut_or_coverageGrowth
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (r c : leftMaskFiber ends m j k l zero p)
    (hrS : r ∈ S) (hcS : c ∈ S)
    (herase : canonicalMaskRightNeighborhood
        ends m j k l zero p (S.erase c) =
      canonicalMaskRightNeighborhood ends m j k l zero p S)
    (hrc : CanonicalTransferWorks ends m k zero r.1.1 c.1.1) :
    ∃ d ∈ S, d ≠ c ∧
      (CanonicalTranslatedRowRootComponentCut
          ends m k zero r.1.1 d.1.1 ∨
        (CanonicalTransferWorks ends m k zero r.1.1 d.1.1 ∧
          CanonicalTightTwoRowCollision ends m j k l zero p c d)) := by
  have _hrS : r ∈ S := hrS
  let q := canonicalTransferMapOfWorks
    ends m j k l zero hloop hjk hkl p r c hrc
  have hqc : q ∈ canonicalMaskRightImages
      ends m j k l zero p c :=
    (mem_canonicalMaskRightImages_iff
      ends m j k l zero p c q).mpr ⟨r, hrc, rfl⟩
  obtain ⟨d, hdS, hdc, hqd⟩ :=
    exists_other_of_erase_canonicalMaskRightNeighborhood_eq
      ends m j k l zero p S c hcS herase q hqc
  exact ⟨d, hdS, hdc,
    canonicalReferenceImage_owner_rootComponentCut_or_works_twoCommon
      hloop hjk hkl r c d hrc hdc.symm hqd⟩


theorem tightFamily_referenceCoverageGrowth_of_no_internalCut
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (r c : leftMaskFiber ends m j k l zero p)
    (hrS : r ∈ S) (hcS : c ∈ S)
    (herase : canonicalMaskRightNeighborhood
        ends m j k l zero p (S.erase c) =
      canonicalMaskRightNeighborhood ends m j k l zero p S)
    (hrc : CanonicalTransferWorks ends m k zero r.1.1 c.1.1)
    (hno : ∀ a ∈ S, ∀ b ∈ S,
      ¬ CanonicalTranslatedRowRootComponentCut
        ends m k zero a.1.1 b.1.1) :
    ∃ d ∈ S, d ≠ c ∧
      CanonicalTransferWorks ends m k zero r.1.1 d.1.1 ∧
      CanonicalTightTwoRowCollision ends m j k l zero p c d := by
  obtain ⟨d, hdS, hdc, hcut | hgrow⟩ :=
    tightFamily_referenceImage_internalCut_or_coverageGrowth
      ends m j k l zero hloop hjk hkl p S r c hrS hcS herase hrc
  · exact False.elim (hno r hrS d hdS hcut)
  · exact ⟨d, hdS, hdc, hgrow⟩


theorem tightFamily_selfImage_internalCut_or_twoCommon
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (c : leftMaskFiber ends m j k l zero p) (hc : c ∈ S)
    (herase : canonicalMaskRightNeighborhood
        ends m j k l zero p (S.erase c) =
      canonicalMaskRightNeighborhood ends m j k l zero p S) :
    ∃ d ∈ S, d ≠ c ∧
      (CanonicalTranslatedRowRootComponentCut
          ends m k zero c.1.1 d.1.1 ∨
        CanonicalTightTwoRowCollision ends m j k l zero p c d) := by
  let q := canonicalTransferMapOfWorks
    ends m j k l zero hloop hjk hkl p c c
      (canonicalTransferWorks_self hloop hjk hkl hk0 c)
  have hqc : q ∈ canonicalMaskRightImages
      ends m j k l zero p c :=
    (mem_canonicalMaskRightImages_iff
      ends m j k l zero p c q).mpr ⟨c,
        canonicalTransferWorks_self hloop hjk hkl hk0 c, rfl⟩
  obtain ⟨d, hdS, hdc, hqd⟩ :=
    exists_other_of_erase_canonicalMaskRightNeighborhood_eq
      ends m j k l zero p S c hc herase q hqc
  exact ⟨d, hdS, hdc,
    canonicalSelfImage_owner_rootComponentCut_or_twoCommon
      hloop hjk hkl hk0 c d hdc.symm hqd⟩

set_option maxHeartbeats 1000000 in


theorem exists_tightFamily_allSelfImage_internalCut_or_twoCommon_of_not_hall
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (hfail : ¬ CanonicalMaskRightHall ends m j k l zero p) :
    ∃ S : Finset (leftMaskFiber ends m j k l zero p),
      S.Nonempty ∧
      (canonicalMaskRightNeighborhood
          ends m j k l zero p S).card + 1 = S.card ∧
      ∀ c ∈ S, ∃ d ∈ S, d ≠ c ∧
        (CanonicalTranslatedRowRootComponentCut
            ends m k zero c.1.1 d.1.1 ∨
          CanonicalTightTwoRowCollision ends m j k l zero p c d) := by
  obtain ⟨S, hSne, htight, herase, -, -, -⟩ :=
    exists_tight_canonicalMaskRightHall_obstruction
      ends m j k l zero hloop hjk hkl hk0 p hfail
  refine ⟨S, hSne, htight, ?_⟩
  intro c hc
  exact tightFamily_selfImage_internalCut_or_twoCommon
    ends m j k l zero hloop hjk hkl hk0 p S c hc (herase c hc)


end StatMech.GrahamGHS.FourColor
