/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferComponentCut.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
import Def.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferMatching.Part16
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem canonicalMaskRightTightRootCutCoverageMerge_of_excluded
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hno : CanonicalMaskRightTightRootCutExcluded
      ends m j k l zero p) :
    CanonicalMaskRightTightRootCutCoverageMerge
      ends m j k l zero p := by
  intro S hSne htight r hrS c hcS hcut
  exact False.elim (hno S hSne htight r hrS c hcS hcut)


theorem canonicalMaskRightHall_of_tightRootCutCoverageMerge
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (hmerge : CanonicalMaskRightTightRootCutCoverageMerge
      ends m j k l zero p) :
    CanonicalMaskRightHall ends m j k l zero p := by
  by_contra hfail
  obtain ⟨S, hSne, htight, -, -, -, -⟩ :=
    exists_tight_canonicalMaskRightHall_obstruction
      ends m j k l zero hloop hjk hkl hk0 p hfail
  classical
  obtain ⟨r, hrS, hrMax⟩ := S.exists_max_image
    (fun x => (canonicalMaskRightRestrictedCoverage
      ends m j k l zero p S x).card) hSne
  by_cases hworks : ∀ d ∈ S,
      CanonicalTransferWorks ends m k zero r.1.1 d.1.1
  · have hle := card_le_canonicalMaskRightNeighborhood_of_reference
      ends m j k l zero hloop hjk hkl p S r hworks
    omega
  · push Not at hworks
    obtain ⟨c, hcS, hbad⟩ := hworks
    have hcut := canonicalTransferWorks_failed_rootComponentCut
      hloop hjk hkl r c hbad
    obtain ⟨t, htS, htMerge⟩ :=
      hmerge S hSne htight r hrS c hcS hcut
    have hsub : canonicalMaskRightRestrictedCoverage
        ends m j k l zero p S r ⊆
        canonicalMaskRightRestrictedCoverage
          ends m j k l zero p S t := by
      intro d hd
      rw [mem_canonicalMaskRightRestrictedCoverage_iff] at hd ⊢
      exact ⟨hd.1, htMerge d hd.1 (Or.inl hd.2)⟩
    have hcNot : c ∉ canonicalMaskRightRestrictedCoverage
        ends m j k l zero p S r := by
      rw [mem_canonicalMaskRightRestrictedCoverage_iff]
      exact fun hc => hbad hc.2
    have hcIn : c ∈ canonicalMaskRightRestrictedCoverage
        ends m j k l zero p S t := by
      rw [mem_canonicalMaskRightRestrictedCoverage_iff]
      exact ⟨hcS, htMerge c hcS (Or.inr
        (canonicalTransferWorks_self hloop hjk hkl hk0 c))⟩
    have hins : insert c (canonicalMaskRightRestrictedCoverage
        ends m j k l zero p S r) ⊆
        canonicalMaskRightRestrictedCoverage
          ends m j k l zero p S t := by
      intro d hd
      rw [Finset.mem_insert] at hd
      rcases hd with rfl | hd
      · exact hcIn
      · exact hsub hd
    have hcard := Finset.card_le_card hins
    rw [Finset.card_insert_of_notMem hcNot] at hcard
    have hlt : (canonicalMaskRightRestrictedCoverage
        ends m j k l zero p S r).card <
        (canonicalMaskRightRestrictedCoverage
          ends m j k l zero p S t).card := by
      omega
    exact (Nat.not_lt_of_ge (hrMax t htS)) hlt


theorem canonicalMaskRightHall_of_tightRootCutExcluded
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (hno : CanonicalMaskRightTightRootCutExcluded
      ends m j k l zero p) :
    CanonicalMaskRightHall ends m j k l zero p := by
  by_contra hfail
  obtain ⟨S, hSne, htight, -, -, -, -⟩ :=
    exists_tight_canonicalMaskRightHall_obstruction
      ends m j k l zero hloop hjk hkl hk0 p hfail
  obtain ⟨r, hrS, c, hcS, hcut⟩ :=
    exists_rootComponentCut_of_tight_canonicalMaskRightNeighborhood
      ends m j k l zero hloop hjk hkl p S hSne htight
  exact hno S hSne htight r hrS c hcS hcut


theorem GrahamFiberMinor_of_no_canonicalTranslatedRowRootComponentCut
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (hno : ∀ (p : Finset I × Finset I)
      (r c : leftMaskFiber ends m j k l zero p),
      ¬ CanonicalTranslatedRowRootComponentCut
        ends m k zero r.1.1 c.1.1) :
    GrahamFiberMinor ends m j k l zero := by
  apply GrahamFiberMinor_of_canonicalMaskRightHall
  intro p
  classical
  exact canonicalMaskRightHall_of_no_rootComponentCut
    ends m j k l zero hloop hjk hkl hk0 p (hno p)


theorem GrahamFiberMinor_of_tightRootCutCoverageMerge
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (hmerge : ∀ p : Finset I × Finset I,
      CanonicalMaskRightTightRootCutCoverageMerge
        ends m j k l zero p) :
    GrahamFiberMinor ends m j k l zero := by
  apply GrahamFiberMinor_of_canonicalMaskRightHall
  intro p
  classical
  exact canonicalMaskRightHall_of_tightRootCutCoverageMerge
    ends m j k l zero hloop hjk hkl hk0 p (hmerge p)


theorem GrahamFiberMinor_of_tightRootCutExcluded
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (hno : ∀ p : Finset I × Finset I,
      CanonicalMaskRightTightRootCutExcluded
        ends m j k l zero p) :
    GrahamFiberMinor ends m j k l zero := by
  apply GrahamFiberMinor_of_canonicalMaskRightHall
  intro p
  classical
  exact canonicalMaskRightHall_of_tightRootCutExcluded
    ends m j k l zero hloop hjk hkl hk0 p (hno p)


theorem exists_canonicalTranslatedRowCycle_obstruction
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (hfail : ¬ CanonicalMaskRightHall ends m j k l zero p) :
    ∃ S : Finset (leftMaskFiber ends m j k l zero p),
      (canonicalMaskRightNeighborhood ends m j k l zero p S).card + 1 =
          S.card ∧
        ∃ c d : ↑S, c ≠ d ∧ ∃ σ : Equiv.Perm ↑S,
          σ c = d ∧
            ∀ x : ↑S, ∃ a b : leftMaskFiber ends m j k l zero p,
              RowSupportDisconnects ends m
                  (canonicalTranslatedRow
                    ends m k zero a.1.1 x.1.1.1) k zero ∧
                canonicalTranslatedRow ends m k zero a.1.1 x.1.1.1 =
                  canonicalTranslatedRow
                    ends m k zero b.1.1 (σ x).1.1.1 := by
  classical
  obtain ⟨S, hSne, htight, -, hproper, -, hadj⟩ :=
    exists_tight_canonicalMaskRightHall_obstruction
      ends m j k l zero hloop hjk hkl hk0 p hfail
  obtain ⟨c, hc⟩ := hSne
  obtain ⟨d, hd, hdc, hcd⟩ := hadj c hc
  obtain ⟨σ, hσcd, hσrows⟩ := exists_canonicalTranslatedRowPerm
    ends m j k l zero hloop hjk hkl p S htight hproper c d hc hd hcd
  refine ⟨S, htight, ⟨c, hc⟩, ⟨d, hd⟩, ?_, σ, hσcd, hσrows⟩
  intro h
  apply hdc
  exact (congrArg Subtype.val h).symm


theorem exists_canonicalTransferFoldCycle_obstruction
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (hfail : ¬ CanonicalMaskRightHall ends m j k l zero p) :
    ∃ S : Finset (leftMaskFiber ends m j k l zero p),
      ∃ σ : Equiv.Perm ↑S,
        σ ≠ Equiv.refl ↑S ∧
          ∃ a b : ↑S -> leftMaskFiber ends m j k l zero p,
            (∀ x, RowSupportDisconnects ends m
              (canonicalTranslatedRow
                ends m k zero (a x).1.1 x.1.1.1) k zero) ∧
            (∀ x, canonicalTranslatedRow
                ends m k zero (a x).1.1 x.1.1.1 =
              canonicalTranslatedRow
                ends m k zero (b x).1.1 (σ x).1.1.1) ∧
            symmDiffFold Finset.univ (fun x =>
                canonicalTransferUnion ends m k zero (a x).1.1) =
              symmDiffFold Finset.univ (fun x =>
                canonicalTransferUnion ends m k zero (b x).1.1) := by
  classical
  obtain ⟨S, -, c, d, hcd, σ, hσcd, hrows⟩ :=
    exists_canonicalTranslatedRowCycle_obstruction
      ends m j k l zero hloop hjk hkl hk0 p hfail
  obtain ⟨a, b, hdisc, heq, hfold⟩ :=
    exists_referenceTransferFold_eq_of_translatedRowPerm
      ends m j k l zero p S σ hrows
  refine ⟨S, σ, ?_, a, b, hdisc, heq, hfold⟩
  intro hσ
  apply hcd
  rw [hσ] at hσcd
  simpa using hσcd

end StatMech.GrahamGHS.FourColor
