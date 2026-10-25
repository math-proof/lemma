/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferComponentCut.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
import Def.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferMatching.Part2
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


@[simp] theorem mem_canonicalWorkingTranslatedRows_iff
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c : leftMaskFiber ends m j k l zero p) (K : Finset I) :
    K ∈ canonicalWorkingTranslatedRows ends m j k l zero p c ↔
      ∃ r : leftMaskFiber ends m j k l zero p,
        CanonicalTransferWorks ends m k zero r.1.1 c.1.1 ∧
          canonicalTranslatedRow ends m k zero r.1.1 c.1.1 = K := by
  classical
  simp [canonicalWorkingTranslatedRows]


theorem image_rowClass_zero_canonicalMaskRightImages
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    (c : leftMaskFiber ends m j k l zero p) :
    (canonicalMaskRightImages ends m j k l zero p c).image
        (fun q => rowClass m q.1.1 0) =
      canonicalWorkingTranslatedRows ends m j k l zero p c := by
  classical
  ext K
  constructor
  · intro hK
    obtain ⟨q, hq, hrow⟩ := Finset.mem_image.mp hK
    obtain ⟨r, hworks, hqraw⟩ := (mem_canonicalMaskRightImages_iff
      ends m j k l zero p c q).mp hq
    rw [mem_canonicalWorkingTranslatedRows_iff]
    refine ⟨r, hworks, ?_⟩
    rw [← hrow, hqraw]
    have hv := canonicalTransfers_valid_on_sameMask hloop hjk hkl r c
    rw [rowClass_balancedSwap_zero hv.1 hv.2.1]
    rfl
  · intro hK
    obtain ⟨r, hworks, hrow⟩ :=
      (mem_canonicalWorkingTranslatedRows_iff
        ends m j k l zero p c K).mp hK
    let q := canonicalTransferMapOfWorks
      ends m j k l zero hloop hjk hkl p r c hworks
    apply Finset.mem_image.mpr
    refine ⟨q, (mem_canonicalMaskRightImages_iff
      ends m j k l zero p c q).mpr ⟨r, hworks, rfl⟩, ?_⟩
    rw [← hrow]
    have hv := canonicalTransfers_valid_on_sameMask hloop hjk hkl r c
    change rowClass m
      (balancedSwap m
        (canonicalMiddleTransfer ends m r.1.1 k zero)
        (canonicalOuterTransfer ends m r.1.1 k zero) c.1.1) 0 = _
    rw [rowClass_balancedSwap_zero hv.1 hv.2.1]
    rfl


theorem card_canonicalMaskRightImages_eq_card_translatedRows
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    (c : leftMaskFiber ends m j k l zero p) :
    (canonicalMaskRightImages ends m j k l zero p c).card =
      (canonicalWorkingTranslatedRows ends m j k l zero p c).card := by
  classical
  calc
    _ = ((canonicalMaskRightImages ends m j k l zero p c).image
        (fun q => rowClass m q.1.1 0)).card :=
      (Finset.card_image_of_injective _
        (rightMaskFiber_rowClass_zero_injective
          ends m j k l zero p)).symm
    _ = _ := congrArg Finset.card
      (image_rowClass_zero_canonicalMaskRightImages
        ends m j k l zero hloop hjk hkl p c)


theorem exists_mem_canonicalMaskRightImages_iff_adjacent
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c d : leftMaskFiber ends m j k l zero p) :
    (∃ q : rightMaskFiber ends m j k l zero p,
      q ∈ canonicalMaskRightImages ends m j k l zero p c ∧
        q ∈ canonicalMaskRightImages ends m j k l zero p d) ↔
      CanonicalMaskTransferAdjacent ends m j k l zero p c d := by
  constructor
  · rintro ⟨q, hqc, hqd⟩
    obtain ⟨a, -, hqa⟩ := (mem_canonicalMaskRightImages_iff
      ends m j k l zero p c q).mp hqc
    obtain ⟨b, -, hqb⟩ := (mem_canonicalMaskRightImages_iff
      ends m j k l zero p d q).mp hqd
    exact ⟨q, a, b, hqa, hqb⟩
  · rintro ⟨q, a, b, hqa, hqb⟩
    have hac : CanonicalTransferWorks ends m k zero a.1.1 c.1.1 := by
      rw [CanonicalTransferWorks, ← hqa]
      exact q.1.2.2.2.2.2
    have hbd : CanonicalTransferWorks ends m k zero b.1.1 d.1.1 := by
      rw [CanonicalTransferWorks, ← hqb]
      exact q.1.2.2.2.2.2
    exact ⟨q,
      (mem_canonicalMaskRightImages_iff
        ends m j k l zero p c q).mpr ⟨a, hac, hqa⟩,
      (mem_canonicalMaskRightImages_iff
        ends m j k l zero p d q).mpr ⟨b, hbd, hqb⟩⟩


theorem canonicalMaskRightImages_disjoint_of_not_orbit
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c d : leftMaskFiber ends m j k l zero p)
    (hcd : ¬ CanonicalMaskTransferOrbit ends m j k l zero p c d) :
    Disjoint
      (canonicalMaskRightImages ends m j k l zero p c)
      (canonicalMaskRightImages ends m j k l zero p d) := by
  classical
  rw [Finset.disjoint_left]
  intro q hqc hqd
  apply hcd
  exact Relation.ReflTransGen.single
    ((exists_mem_canonicalMaskRightImages_iff_adjacent
      ends m j k l zero p c d).mp ⟨q, hqc, hqd⟩)


end StatMech.GrahamGHS.FourColor
