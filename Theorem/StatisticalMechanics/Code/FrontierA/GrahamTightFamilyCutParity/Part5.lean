/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTightFamilyCutParity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyRootCollision
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalCollisionSquare
import Def.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyCutParity.Part4
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem exists_normalizedBoundaryRow_of_exclusiveBoundaryCertificate
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {p : Finset I × Finset I}
    (a b c : leftMaskFiber ends m j k l zero p)
    (hcert : CanonicalCoverageExclusiveBoundaryCertificate
      ends m j k l zero p a b c) :
    ∃ rho : Fin 2, CanonicalCoverageNormalizedBoundaryRow
      ends m j k l zero
        (canonicalQuadrangleCompletion ends m k zero
          a.1.1 b.1.1 c.1.1) rho := by
  rcases canonicalCoverageExclusiveBoundaryCertificate_zeroRootNormalized
      a b c hcert with hzero | hone
  · exact ⟨0, by simpa [CanonicalCoverageNormalizedBoundaryRow] using hzero⟩
  · exact ⟨1, by simpa [CanonicalCoverageNormalizedBoundaryRow] using hone⟩


theorem normalizedBoundaryRow_component_ne_other_complement
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (d e : ↑m -> Fin 4) (rho sigma : Fin 2)
    (hd : CanonicalCoverageNormalizedBoundaryRow
      ends m j k l zero d rho)
    (he : CanonicalCoverageNormalizedBoundaryRow
      ends m j k l zero e sigma) :
    edgeComponent ends (rowClass m d rho) zero ≠
      rowClass m e sigma \
        edgeComponent ends (rowClass m e sigma) zero := by
  intro heq
  have hs := congrArg (StatMech.Sharpness.RandomCurrent.sources ends) heq
  rw [hd.2.1, he.2.2.1] at hs
  fin_cases rho <;> simp at hs


theorem opposingQuadrangle_rowClass_eq_iff
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (a b c d : leftMaskFiber ends m j k l zero p) (rho : Fin 2) :
    rowClass m
        (canonicalQuadrangleCompletion ends m k zero
          a.1.1 b.1.1 c.1.1) rho =
        rowClass m
          (canonicalQuadrangleCompletion ends m k zero
            b.1.1 a.1.1 d.1.1) rho ↔
      rowClass m c.1.1 rho = rowClass m d.1.1 rho := by
  rw [rowClass_canonicalQuadrangleCompletion hloop hjk hkl a b c rho,
    rowClass_canonicalQuadrangleCompletion hloop hjk hkl b a d rho]
  have hreorder :
      rowClass m d.1.1 rho ∆
          canonicalTransferUnion ends m k zero b.1.1 ∆
          canonicalTransferUnion ends m k zero a.1.1 =
        rowClass m d.1.1 rho ∆
          canonicalTransferUnion ends m k zero a.1.1 ∆
          canonicalTransferUnion ends m k zero b.1.1 := by
    ac_rfl
  rw [hreorder, symmDiff_left_inj, symmDiff_left_inj]


theorem opposingExclusiveBadQuadrangles_rowZero_ne
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (r y d : leftMaskFiber ends m j k l zero p)
    (hy : y ∈ canonicalCoverageExclusiveBadQuadrangles
      ends m j k l zero p y r)
    (hd : d ∈ canonicalCoverageExclusiveBadQuadrangles
      ends m j k l zero p r y) :
    rowClass m
        (canonicalQuadrangleCompletion ends m k zero
          y.1.1 r.1.1 y.1.1) 0 ≠
      rowClass m
        (canonicalQuadrangleCompletion ends m k zero
          r.1.1 y.1.1 d.1.1) 0 := by
  have hy' := (mem_canonicalCoverageExclusiveBadQuadrangles_iff
    ends m j k l zero p y r y).mp hy
  have hd' := (mem_canonicalCoverageExclusiveBadQuadrangles_iff
    ends m j k l zero p r y d).mp hd
  intro hrow
  have hydRow : rowClass m y.1.1 0 = rowClass m d.1.1 0 :=
    (opposingQuadrangle_rowClass_eq_iff
      hloop hjk hkl y r y d 0).mp hrow
  have hyd : y = d := leftMaskFiber_rowClass_zero_injective
    ends m j k l zero p hydRow
  subst d
  exact hy'.2.1 hd'.1

set_option maxHeartbeats 1000000 in


theorem incomparableRestrictedCoverage_controlledOwnerDichotomies
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (herase : ∀ x ∈ S, canonicalMaskRightNeighborhood
        ends m j k l zero p (S.erase x) =
      canonicalMaskRightNeighborhood ends m j k l zero p S)
    (r c : leftMaskFiber ends m j k l zero p)
    (hrS : r ∈ S) (hcS : c ∈ S)
    (hrc : ¬ canonicalMaskRightRestrictedCoverage
        ends m j k l zero p S r ⊆
      canonicalMaskRightRestrictedCoverage ends m j k l zero p S c)
    (hcr : ¬ canonicalMaskRightRestrictedCoverage
        ends m j k l zero p S c ⊆
      canonicalMaskRightRestrictedCoverage ends m j k l zero p S r) :
    ∃ d ∈ S, ∃ e ∈ S,
      CanonicalTransferWorks ends m k zero r.1.1 d.1.1 ∧
      ¬ CanonicalTransferWorks ends m k zero c.1.1 d.1.1 ∧
      CanonicalTransferWorks ends m k zero c.1.1 e.1.1 ∧
      ¬ CanonicalTransferWorks ends m k zero r.1.1 e.1.1 ∧
      (∃ u ∈ S, u ≠ d ∧
        (CanonicalTranslatedRowRootComponentCut
            ends m k zero r.1.1 u.1.1 ∨
          (CanonicalTransferWorks ends m k zero r.1.1 u.1.1 ∧
            CanonicalTightTwoRowCollision ends m j k l zero p d u))) ∧
      ∃ v ∈ S, v ≠ e ∧
        (CanonicalTranslatedRowRootComponentCut
            ends m k zero c.1.1 v.1.1 ∨
          (CanonicalTransferWorks ends m k zero c.1.1 v.1.1 ∧
            CanonicalTightTwoRowCollision ends m j k l zero p e v)) := by
  obtain ⟨⟨d, hdS, hrd, hcd⟩, ⟨e, heS, hce, hre⟩⟩ :=
    exists_restrictedCoverage_exclusiveWitnesses_of_incomparable
      ends m j k l zero p S r c hrc hcr
  obtain ⟨u, huS, hud, hu⟩ :=
    tightFamily_referenceImage_internalCut_or_coverageGrowth
      ends m j k l zero hloop hjk hkl p S r d hrS hdS
        (herase d hdS) hrd
  obtain ⟨v, hvS, hve, hv⟩ :=
    tightFamily_referenceImage_internalCut_or_coverageGrowth
      ends m j k l zero hloop hjk hkl p S c e hcS heS
        (herase e heS) hce
  exact ⟨d, hdS, e, heS, hrd, hcd, hce, hre,
    ⟨u, huS, hud, hu⟩, v, hvS, hve, hv⟩

set_option maxHeartbeats 1000000 in


theorem exists_tightFamily_incomparableRootCut_of_not_hall
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (hfail : ¬ CanonicalMaskRightHall ends m j k l zero p) :
    ∃ S : Finset (leftMaskFiber ends m j k l zero p),
      S.Nonempty ∧
      (canonicalMaskRightNeighborhood
          ends m j k l zero p S).card + 1 = S.card ∧
      (∀ x ∈ S, canonicalMaskRightNeighborhood
          ends m j k l zero p (S.erase x) =
        canonicalMaskRightNeighborhood ends m j k l zero p S) ∧
      (∀ x ∈ S, ∀ y ∈ S,
        CanonicalMaskTransferOrbit ends m j k l zero p x y) ∧
      ∃ r ∈ S, ∃ c ∈ S,
        CanonicalTranslatedRowRootComponentCut
            ends m k zero r.1.1 c.1.1 ∧
        ¬ canonicalMaskRightRestrictedCoverage
            ends m j k l zero p S r ⊆
          canonicalMaskRightRestrictedCoverage
            ends m j k l zero p S c ∧
        ¬ canonicalMaskRightRestrictedCoverage
            ends m j k l zero p S c ⊆
          canonicalMaskRightRestrictedCoverage
            ends m j k l zero p S r := by
  classical
  obtain ⟨S, hSne, htight, herase, -, horbit, -⟩ :=
    exists_tight_canonicalMaskRightHall_obstruction
      ends m j k l zero hloop hjk hkl hk0 p hfail
  obtain ⟨r, hrS, hrMax⟩ := S.exists_max_image
    (fun x => (canonicalMaskRightRestrictedCoverage
      ends m j k l zero p S x).card) hSne
  by_cases hworks : ∀ d ∈ S,
      CanonicalTransferWorks ends m k zero r.1.1 d.1.1
  · have hle := card_le_canonicalMaskRightNeighborhood_of_reference
      ends m j k l zero hloop hjk hkl p S r hworks
    omega
  · push Not at hworks
    obtain ⟨c, hcS, hrcBad⟩ := hworks
    have hcut := canonicalTransferWorks_failed_rootComponentCut
      hloop hjk hkl r c hrcBad
    have hcNotR : c ∉ canonicalMaskRightRestrictedCoverage
        ends m j k l zero p S r := by
      rw [mem_canonicalMaskRightRestrictedCoverage_iff]
      exact fun hc => hrcBad hc.2
    have hcInC : c ∈ canonicalMaskRightRestrictedCoverage
        ends m j k l zero p S c := by
      rw [mem_canonicalMaskRightRestrictedCoverage_iff]
      exact ⟨hcS, canonicalTransferWorks_self hloop hjk hkl hk0 c⟩
    have hCR : ¬ canonicalMaskRightRestrictedCoverage
        ends m j k l zero p S c ⊆
      canonicalMaskRightRestrictedCoverage ends m j k l zero p S r :=
      fun hsub => hcNotR (hsub hcInC)
    have hRC : ¬ canonicalMaskRightRestrictedCoverage
        ends m j k l zero p S r ⊆
      canonicalMaskRightRestrictedCoverage ends m j k l zero p S c := by
      intro hsub
      have hins : insert c (canonicalMaskRightRestrictedCoverage
          ends m j k l zero p S r) ⊆
          canonicalMaskRightRestrictedCoverage
            ends m j k l zero p S c := by
        intro d hd
        rw [Finset.mem_insert] at hd
        rcases hd with rfl | hd
        · exact hcInC
        · exact hsub hd
      have hcard := Finset.card_le_card hins
      rw [Finset.card_insert_of_notMem hcNotR] at hcard
      have hmax := hrMax c hcS
      omega
    exact ⟨S, hSne, htight, herase, horbit,
      r, hrS, c, hcS, hcut, hRC, hCR⟩


theorem exists_secondCommonImage_iff_canonicalTightTwoRowCollision
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c d : leftMaskFiber ends m j k l zero p)
    (q : rightMaskFiber ends m j k l zero p)
    (hqc : q ∈ canonicalMaskRightImages ends m j k l zero p c)
    (hqd : q ∈ canonicalMaskRightImages ends m j k l zero p d) :
    (∃ r : rightMaskFiber ends m j k l zero p,
        r ≠ q ∧
        r ∈ canonicalMaskRightImages ends m j k l zero p c ∧
        r ∈ canonicalMaskRightImages ends m j k l zero p d) ↔
      CanonicalTightTwoRowCollision ends m j k l zero p c d := by
  constructor
  · rintro ⟨r, hrq, hrc, hrd⟩
    exact ⟨q, r, hrq.symm, hqc, hqd, hrc, hrd⟩
  · rintro ⟨q1, q2, hq12, hq1c, hq1d, hq2c, hq2d⟩
    by_cases hq1q : q1 = q
    · refine ⟨q2, ?_, hq2c, hq2d⟩
      intro hq2q
      exact hq12 (hq1q.trans hq2q.symm)
    · exact ⟨q1, hq1q, hq1c, hq1d⟩


theorem common_canonicalMaskRightImage_eq_of_not_twoRowCollision
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c d : leftMaskFiber ends m j k l zero p)
    (hno : ¬ CanonicalTightTwoRowCollision ends m j k l zero p c d)
    (q r : rightMaskFiber ends m j k l zero p)
    (hqc : q ∈ canonicalMaskRightImages ends m j k l zero p c)
    (hqd : q ∈ canonicalMaskRightImages ends m j k l zero p d)
    (hrc : r ∈ canonicalMaskRightImages ends m j k l zero p c)
    (hrd : r ∈ canonicalMaskRightImages ends m j k l zero p d) :
    r = q := by
  by_contra hrq
  exact hno ((exists_secondCommonImage_iff_canonicalTightTwoRowCollision
    ends m j k l zero p c d q hqc hqd).mp ⟨r, hrq, hrc, hrd⟩)

set_option maxHeartbeats 1000000 in


theorem canonicalMaskRightAugmentedRootCollision_opposingAtRight_or_reroute
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (c : ↑S)
    (f : canonicalMaskRightAugmentedEquivType
      ends m j k l zero p S)
    (hf : CanonicalMaskRightAugmentedMatching
      ends m j k l zero p S c f)
    (q : ↑(canonicalMaskRightNeighborhood ends m j k l zero p S))
    (hqc : q.1 ∈ canonicalMaskRightImages
      ends m j k l zero p c.1) :
    (∃ d : ↑S, d ≠ c ∧ f d = some q ∧
      CanonicalOpposingRootCutsAtRight
        ends m j k l zero p c.1 d.1 q.1) ∨
      ∃ e : ↑S, e ≠ c ∧
        ∃ g : canonicalMaskRightAugmentedEquivType
            ends m j k l zero p S,
          CanonicalMaskRightAugmentedMatching
            ends m j k l zero p S e g := by
  classical
  let d : ↑S := f.symm (some q)
  have hfd : f d = some q := by simp [d]
  have hdc : d ≠ c := by
    intro h
    have hnone : f d = none := (congrArg f h).trans hf.1
    rw [hnone] at hfd
    cases hfd
  obtain ⟨s, hfs, hsd⟩ := hf.2 d hdc
  have hsq : s = q := Option.some.inj (hfs.symm.trans hfd)
  have hqd : q.1 ∈ canonicalMaskRightImages
      ends m j k l zero p d.1 := by
    simpa only [hsq] using hsd
  have hcd : c.1 ≠ d.1 := by
    intro h
    exact hdc (Subtype.ext h.symm)
  rcases canonicalCommonImage_opposingAtRight_or_twoCommon
      hloop hjk hkl c.1 d.1 hcd q.1 hqc hqd with hcuts | hsquare
  · exact Or.inl ⟨d, hdc, hfd, hcuts⟩
  · obtain ⟨r, hrq, hrc, hrd⟩ :=
      (exists_secondCommonImage_iff_canonicalTightTwoRowCollision
        ends m j k l zero p c.1 d.1 q.1 hqc hqd).mpr hsquare
    have hrS : r ∈ canonicalMaskRightNeighborhood
        ends m j k l zero p S :=
      (mem_canonicalMaskRightNeighborhood_iff
        ends m j k l zero p S r).mpr ⟨c.1, c.2, hrc⟩
    let rS : ↑(canonicalMaskRightNeighborhood
        ends m j k l zero p S) := ⟨r, hrS⟩
    have hqrS : q ≠ rS := by
      intro h
      exact hrq (congrArg Subtype.val h).symm
    obtain ⟨e, hec, -, -, g, hg⟩ :=
      canonicalMaskRightAugmentedMatching_rotateAssignedSecondRow
        ends m j k l zero p S c d hdc f hf q rS hfd hqrS hqc hrd
    exact Or.inr ⟨e, hec, g, hg⟩

set_option maxHeartbeats 1000000 in


theorem canonicalMaskRightAugmentedSelfImage_internalCut_or_reroute
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (c : ↑S)
    (f : canonicalMaskRightAugmentedEquivType
      ends m j k l zero p S)
    (hf : CanonicalMaskRightAugmentedMatching
      ends m j k l zero p S c f) :
    (∃ d : ↑S, d ≠ c ∧
      CanonicalTranslatedRowRootComponentCut
        ends m k zero c.1.1.1 d.1.1.1) ∨
      ∃ e : ↑S, e ≠ c ∧
        ∃ g : canonicalMaskRightAugmentedEquivType
            ends m j k l zero p S,
          CanonicalMaskRightAugmentedMatching
            ends m j k l zero p S e g := by
  classical
  let q0 := canonicalTransferMapOfWorks
    ends m j k l zero hloop hjk hkl p c.1 c.1
      (canonicalTransferWorks_self hloop hjk hkl hk0 c.1)
  have hq0c : q0 ∈ canonicalMaskRightImages
      ends m j k l zero p c.1 :=
    (mem_canonicalMaskRightImages_iff
      ends m j k l zero p c.1 q0).mpr ⟨c.1,
        canonicalTransferWorks_self hloop hjk hkl hk0 c.1, rfl⟩
  have hq0N : q0 ∈ canonicalMaskRightNeighborhood
      ends m j k l zero p S :=
    (mem_canonicalMaskRightNeighborhood_iff
      ends m j k l zero p S q0).mpr ⟨c.1, c.2, hq0c⟩
  let q : ↑(canonicalMaskRightNeighborhood
      ends m j k l zero p S) := ⟨q0, hq0N⟩
  let d : ↑S := f.symm (some q)
  have hfd : f d = some q := by simp [d]
  have hdc : d ≠ c := by
    intro h
    have hnone : f d = none := (congrArg f h).trans hf.1
    rw [hnone] at hfd
    cases hfd
  obtain ⟨s, hfs, hsd⟩ := hf.2 d hdc
  have hsq : s = q := Option.some.inj (hfs.symm.trans hfd)
  have hq0d : q0 ∈ canonicalMaskRightImages
      ends m j k l zero p d.1 := by
    simpa only [q, hsq] using hsd
  have hcd : c.1 ≠ d.1 := by
    intro h
    exact hdc (Subtype.ext h.symm)
  rcases canonicalSelfImage_owner_rootComponentCut_or_twoCommon
      hloop hjk hkl hk0 c.1 d.1 hcd hq0d with hcut | hsquare
  · exact Or.inl ⟨d, hdc, hcut⟩
  · obtain ⟨r, hrq0, hrc, hrd⟩ :=
      (exists_secondCommonImage_iff_canonicalTightTwoRowCollision
        ends m j k l zero p c.1 d.1 q0 hq0c hq0d).mpr hsquare
    have hrN : r ∈ canonicalMaskRightNeighborhood
        ends m j k l zero p S :=
      (mem_canonicalMaskRightNeighborhood_iff
        ends m j k l zero p S r).mpr ⟨c.1, c.2, hrc⟩
    let rN : ↑(canonicalMaskRightNeighborhood
        ends m j k l zero p S) := ⟨r, hrN⟩
    have hqr : q ≠ rN := by
      intro h
      exact hrq0 (congrArg Subtype.val h).symm
    obtain ⟨e, hec, -, -, g, hg⟩ :=
      canonicalMaskRightAugmentedMatching_rotateAssignedSecondRow
        ends m j k l zero p S c d hdc f hf q rN hfd hqr hq0c hrd
    exact Or.inr ⟨e, hec, g, hg⟩

set_option maxHeartbeats 1000000 in


theorem canonicalConsecutiveTriple_twoRow_or_chord_or_escape
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (hproper : ∀ T : Finset (leftMaskFiber ends m j k l zero p),
      T ⊂ S -> T.card ≤
        (canonicalMaskRightNeighborhood ends m j k l zero p T).card)
    (herase : ∀ x ∈ S, canonicalMaskRightNeighborhood
        ends m j k l zero p (S.erase x) =
      canonicalMaskRightNeighborhood ends m j k l zero p S)
    (c d e : leftMaskFiber ends m j k l zero p)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e)
    (htriple : ({c, d, e} : Finset
      (leftMaskFiber ends m j k l zero p)) ⊂ S)
    (q r : rightMaskFiber ends m j k l zero p)
    (hqc : q ∈ canonicalMaskRightImages ends m j k l zero p c)
    (hqd : q ∈ canonicalMaskRightImages ends m j k l zero p d)
    (hrd : r ∈ canonicalMaskRightImages ends m j k l zero p d)
    (hre : r ∈ canonicalMaskRightImages ends m j k l zero p e) :
    CanonicalTightTwoRowCollision ends m j k l zero p c d ∨
      CanonicalTightTwoRowCollision ends m j k l zero p d e ∨
      ∃ x ∈ ({c, d, e} : Finset
          (leftMaskFiber ends m j k l zero p)),
        ∃ y ∈ S, y ≠ x ∧
          ∃ s : rightMaskFiber ends m j k l zero p,
            s ≠ q ∧ s ≠ r ∧
            s ∈ canonicalMaskRightImages ends m j k l zero p x ∧
            s ∈ canonicalMaskRightImages ends m j k l zero p y ∧
            ((x = c ∧ y = e) ∨ (x = e ∧ y = c) ∨
              y ∉ ({c, d, e} : Finset
                (leftMaskFiber ends m j k l zero p))) := by
  classical
  by_cases hCD : CanonicalTightTwoRowCollision
      ends m j k l zero p c d
  · exact Or.inl hCD
  by_cases hDE : CanonicalTightTwoRowCollision
      ends m j k l zero p d e
  · exact Or.inr (Or.inl hDE)
  right
  right
  have hcard : 2 < ({c, d, e} : Finset
      (leftMaskFiber ends m j k l zero p)).card := by
    simp [hcd, hce, hde]
  obtain ⟨x, hxT, s, hsx, hsq, hsr⟩ :=
    exists_canonicalMaskRightNeighbor_ne_pair_of_properHall
      ends m j k l zero p S hproper {c, d, e} htriple hcard q r
  have hxS : x ∈ S := htriple.subset hxT
  obtain ⟨y, hyS, hyx, hsy⟩ :=
    exists_other_of_erase_canonicalMaskRightNeighborhood_eq
      ends m j k l zero p S x hxS (herase x hxS) s hsx
  have hsquareCD
      (hsc : s ∈ canonicalMaskRightImages ends m j k l zero p c)
      (hsd : s ∈ canonicalMaskRightImages ends m j k l zero p d) :
      CanonicalTightTwoRowCollision ends m j k l zero p c d :=
    (exists_secondCommonImage_iff_canonicalTightTwoRowCollision
      ends m j k l zero p c d q hqc hqd).mp ⟨s, hsq, hsc, hsd⟩
  have hsquareDE
      (hsd : s ∈ canonicalMaskRightImages ends m j k l zero p d)
      (hse : s ∈ canonicalMaskRightImages ends m j k l zero p e) :
      CanonicalTightTwoRowCollision ends m j k l zero p d e :=
    (exists_secondCommonImage_iff_canonicalTightTwoRowCollision
      ends m j k l zero p d e r hrd hre).mp ⟨s, hsr, hsd, hse⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxT
  rcases hxT with hxc | hxd | hxe
  · subst x
    by_cases hyT : y ∈ ({c, d, e} : Finset
        (leftMaskFiber ends m j k l zero p))
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hyT
      rcases hyT with hyc | hyd | hye
      · exact False.elim (hyx hyc)
      · subst y
        exact False.elim (hCD (hsquareCD hsx hsy))
      · exact ⟨c, by simp, y, hyS, hyx, s, hsq, hsr, hsx, hsy,
          Or.inl ⟨rfl, hye⟩⟩
    · exact ⟨c, by simp, y, hyS, hyx, s, hsq, hsr, hsx, hsy,
        Or.inr (Or.inr hyT)⟩
  · subst x
    by_cases hyT : y ∈ ({c, d, e} : Finset
        (leftMaskFiber ends m j k l zero p))
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hyT
      rcases hyT with hyc | hyd | hye
      · subst y
        exact False.elim (hCD (hsquareCD hsy hsx))
      · exact False.elim (hyx hyd)
      · subst y
        exact False.elim (hDE (hsquareDE hsx hsy))
    · exact ⟨d, by simp, y, hyS, hyx, s, hsq, hsr, hsx, hsy,
        Or.inr (Or.inr hyT)⟩
  · subst x
    by_cases hyT : y ∈ ({c, d, e} : Finset
        (leftMaskFiber ends m j k l zero p))
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hyT
      rcases hyT with hyc | hyd | hye
      · exact ⟨e, by simp, y, hyS, hyx, s, hsq, hsr, hsx, hsy,
          Or.inr (Or.inl ⟨rfl, hyc⟩)⟩
      · subst y
        exact False.elim (hDE (hsquareDE hsy hsx))
      · exact False.elim (hyx hye)
    · exact ⟨e, by simp, y, hyS, hyx, s, hsq, hsr, hsx, hsy,
        Or.inr (Or.inr hyT)⟩

set_option maxHeartbeats 1000000 in


theorem exists_twoRowCollision_of_tight_canonicalMaskRightNeighborhood
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (htight : (canonicalMaskRightNeighborhood
        ends m j k l zero p S).card + 1 = S.card) :
    ∃ c ∈ S, ∃ d ∈ S, c ≠ d ∧
      CanonicalTightTwoRowCollision ends m j k l zero p c d := by
  classical
  let selfImage : ↑S ->
      ↑(canonicalMaskRightNeighborhood ends m j k l zero p S) :=
    fun c =>
      let q := canonicalTransferMapOfWorks
        ends m j k l zero hloop hjk hkl p c.1 c.1
          (canonicalTransferWorks_self hloop hjk hkl hk0 c.1)
      ⟨q, (mem_canonicalMaskRightNeighborhood_iff
        ends m j k l zero p S q).mpr ⟨c.1, c.2,
          (mem_canonicalMaskRightImages_iff
            ends m j k l zero p c.1 q).mpr
              ⟨c.1, canonicalTransferWorks_self
                hloop hjk hkl hk0 c.1, rfl⟩⟩⟩
  have hnotinj : ¬ Function.Injective selfImage := by
    intro hinj
    have hcard := Fintype.card_le_of_injective selfImage hinj
    simp only [Fintype.card_coe] at hcard
    omega
  obtain ⟨c, d, hself, hcd⟩ := Function.not_injective_iff.mp hnotinj
  have himage :
      (canonicalTransferMapOfWorks
        ends m j k l zero hloop hjk hkl p c.1 c.1
          (canonicalTransferWorks_self hloop hjk hkl hk0 c.1)).1.1 =
      (canonicalTransferMapOfWorks
        ends m j k l zero hloop hjk hkl p d.1 d.1
          (canonicalTransferWorks_self hloop hjk hkl hk0 d.1)).1.1 := by
    exact congrArg (fun q => q.1.1.1) hself
  exact ⟨c.1, c.2, d.1, d.2, fun h => hcd (Subtype.ext h),
    canonicalSelfTransfer_collision_twoCommonImages
      ends m j k l zero hloop hjk hkl hk0 p c.1 d.1
        (fun h => hcd (Subtype.ext h)) himage⟩

set_option maxHeartbeats 1000000 in


theorem canonicalCollisionPerm_twoCycle_twoRow
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (σ : Equiv.Perm ↑S)
    (Q : ↑S -> rightMaskFiber ends m j k l zero p)
    (hQ : ∀ x,
      Q x ∈ canonicalMaskRightImages ends m j k l zero p x.1 ∧
      Q x ∈ canonicalMaskRightImages ends m j k l zero p (σ x).1)
    (x : ↑S) (hcycle : σ (σ x) = x)
    (hlabels : Q x ≠ Q (σ x)) :
    CanonicalTightTwoRowCollision
      ends m j k l zero p x.1 (σ x).1 := by
  have hq2x : Q (σ x) ∈
      canonicalMaskRightImages ends m j k l zero p x.1 := by
    have hxval : (σ (σ x)).1 = x.1 := congrArg Subtype.val hcycle
    exact hxval ▸ (hQ (σ x)).2
  exact ⟨Q x, Q (σ x), hlabels, (hQ x).1, (hQ x).2,
    hq2x, (hQ (σ x)).1⟩

set_option maxHeartbeats 1000000 in


theorem canonicalCollisionPerm_secondIterate_ne_of_noTwoRow
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (σ : Equiv.Perm ↑S)
    (Q : ↑S -> rightMaskFiber ends m j k l zero p)
    (hQ : ∀ x,
      Q x ∈ canonicalMaskRightImages ends m j k l zero p x.1 ∧
      Q x ∈ canonicalMaskRightImages ends m j k l zero p (σ x).1)
    (hQinj : Function.Injective Q)
    (hno : ∀ x, ¬ CanonicalTightTwoRowCollision
      ends m j k l zero p x.1 (σ x).1)
    (x : ↑S) (hx : σ x ≠ x) :
    σ (σ x) ≠ x := by
  intro hcycle
  have hlabels : Q x ≠ Q (σ x) := by
    intro h
    exact hx (hQinj h.symm)
  exact hno x (canonicalCollisionPerm_twoCycle_twoRow
    ends m j k l zero p S σ Q hQ x hcycle hlabels)

set_option maxHeartbeats 1000000 in


theorem canonicalInjectiveCollisionPerm_opposingCuts_and_no_twoCycles
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (σ : Equiv.Perm ↑S) (hσ : ∀ x, σ x ≠ x)
    (Q : ↑S -> rightMaskFiber ends m j k l zero p)
    (hQ : ∀ x,
      Q x ∈ canonicalMaskRightImages ends m j k l zero p x.1 ∧
      Q x ∈ canonicalMaskRightImages ends m j k l zero p (σ x).1)
    (hQinj : Function.Injective Q)
    (hno : ∀ x, ¬ CanonicalTightTwoRowCollision
      ends m j k l zero p x.1 (σ x).1) :
    (∀ x, CanonicalOpposingRootCutsAtRight
      ends m j k l zero p x.1 (σ x).1 (Q x)) ∧
      ∀ x, σ (σ x) ≠ x := by
  constructor
  · intro x
    have hxne : x.1 ≠ (σ x).1 := by
      intro h
      exact hσ x (Subtype.ext h.symm)
    rcases canonicalCommonImage_opposingAtRight_or_twoCommon
        hloop hjk hkl x.1 (σ x).1 hxne (Q x) (hQ x).1 (hQ x).2 with
      hcuts | hsquare
    · exact hcuts
    · exact False.elim (hno x hsquare)
  · intro x
    exact canonicalCollisionPerm_secondIterate_ne_of_noTwoRow
      ends m j k l zero p S σ Q hQ hQinj hno x (hσ x)

set_option maxHeartbeats 1000000 in


theorem canonicalCollisionIndexPerm_opposingAtRight_or_square
    {A : Type*} [Fintype A]
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (σ : Equiv.Perm A)
    (X : A -> leftMaskFiber ends m j k l zero p)
    (hX : ∀ x, X x ≠ X (σ x))
    (Q : A -> rightMaskFiber ends m j k l zero p)
    (hQ : ∀ x,
      Q x ∈ canonicalMaskRightImages ends m j k l zero p (X x) ∧
      Q x ∈ canonicalMaskRightImages ends m j k l zero p (X (σ x))) :
    (∃ x, CanonicalTightTwoRowCollision
      ends m j k l zero p (X x) (X (σ x))) ∨
      ∀ x, CanonicalOpposingRootCutsAtRight
        ends m j k l zero p (X x) (X (σ x)) (Q x) := by
  by_cases hsquare : ∃ x, CanonicalTightTwoRowCollision
      ends m j k l zero p (X x) (X (σ x))
  · exact Or.inl hsquare
  · right
    intro x
    rcases canonicalCommonImage_opposingAtRight_or_twoCommon
        hloop hjk hkl (X x) (X (σ x)) (hX x)
        (Q x) (hQ x).1 (hQ x).2 with hcuts | hs
    · exact hcuts
    · exact False.elim (hsquare ⟨x, hs⟩)

set_option maxHeartbeats 1000000 in


theorem exists_hallFailure_labelledCollisionPerm
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (hfail : ¬ CanonicalMaskRightHall ends m j k l zero p) :
    ∃ S : Finset (leftMaskFiber ends m j k l zero p),
      ∃ σ : Equiv.Perm ↑S, σ ≠ Equiv.refl ↑S ∧
        ∀ x : ↑S, σ x ≠ x ->
          ∃ q : rightMaskFiber ends m j k l zero p,
            q ∈ canonicalMaskRightImages ends m j k l zero p x.1 ∧
            q ∈ canonicalMaskRightImages ends m j k l zero p (σ x).1 ∧
            (CanonicalOpposingRootCutsAtRight
                ends m j k l zero p x.1 (σ x).1 q ∨
              CanonicalTightTwoRowCollision
                ends m j k l zero p x.1 (σ x).1) := by
  classical
  obtain ⟨S, hSne, htight, -, hproper, -, hadj⟩ :=
    exists_tight_canonicalMaskRightHall_obstruction
      ends m j k l zero hloop hjk hkl hk0 p hfail
  obtain ⟨c, hc⟩ := hSne
  obtain ⟨d, hd, hdc, hcd⟩ := hadj c hc
  obtain ⟨σ, hσcd, hσadj⟩ := exists_canonicalMaskTransferAdjacentPerm
    ends m j k l zero p S htight hproper c d hc hd hcd
  have hσne : σ ≠ Equiv.refl ↑S := by
    intro h
    have hfix : σ ⟨c, hc⟩ = ⟨c, hc⟩ := by simp [h]
    exact hdc (congrArg Subtype.val (hσcd.symm.trans hfix))
  refine ⟨S, σ, hσne, ?_⟩
  intro x hx
  obtain ⟨q, hqx, hqσ⟩ :=
    (exists_mem_canonicalMaskRightImages_iff_adjacent
      ends m j k l zero p x.1 (σ x).1).mpr (hσadj x)
  have hxne : x.1 ≠ (σ x).1 := by
    intro h
    exact hx (Subtype.ext h.symm)
  exact ⟨q, hqx, hqσ,
    canonicalCommonImage_opposingAtRight_or_twoCommon
      hloop hjk hkl x.1 (σ x).1 hxne q hqx hqσ⟩

set_option maxHeartbeats 1000000 in


theorem canonicalCommonImage_explicitOppositeCut_or_twoCommon
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (c d : leftMaskFiber ends m j k l zero p) (hcd : c ≠ d)
    (q : rightMaskFiber ends m j k l zero p)
    (hqc : q ∈ canonicalMaskRightImages ends m j k l zero p c)
    (hqd : q ∈ canonicalMaskRightImages ends m j k l zero p d) :
    CanonicalRowSupportRootComponentCut ends m k zero
        (canonicalCollisionOppositeRow m q.1.1 c.1.1 d.1.1) ∨
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
  by_cases hbc : CanonicalTransferWorks ends m k zero b.1.1 c.1.1
  · exact Or.inr
      (exists_two_common_canonicalMaskRightImages_of_collisionSquare
        hloop hjk hkl a b c d hcd hac htrans hbc)
  · left
    have hcut := canonicalTransferWorks_failed_rootComponentCut
      hloop hjk hkl b c hbc
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
    unfold CanonicalTranslatedRowRootComponentCut at hcut
    unfold CanonicalRowSupportRootComponentCut
    rw [← hexp]
    exact hcut

set_option maxHeartbeats 1000000 in


theorem canonicalFixedPointFreeCollisionPerm_explicitCuts_or_square
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (σ : Equiv.Perm ↑S) (hσ : ∀ x, σ x ≠ x)
    (Q : ↑S -> rightMaskFiber ends m j k l zero p)
    (hQ : ∀ x,
      Q x ∈ canonicalMaskRightImages ends m j k l zero p x.1 ∧
      Q x ∈ canonicalMaskRightImages ends m j k l zero p (σ x).1) :
    (∃ x, CanonicalTightTwoRowCollision
      ends m j k l zero p x.1 (σ x).1) ∨
      ((∀ x, CanonicalRowSupportRootComponentCut ends m k zero
        (canonicalCollisionOppositeRow
          m (Q x).1.1 x.1.1.1 (σ x).1.1.1)) ∧
        symmDiffFold Finset.univ (fun x =>
            canonicalCollisionOppositeRow
              m (Q x).1.1 x.1.1.1 (σ x).1.1.1) =
          symmDiffFold Finset.univ
            (fun x => rowClass m (Q x).1.1 0)) := by
  classical
  by_cases hsquare : ∃ x, CanonicalTightTwoRowCollision
      ends m j k l zero p x.1 (σ x).1
  · exact Or.inl hsquare
  · right
    constructor
    · intro x
      have hxne : x.1 ≠ (σ x).1 := by
        intro h
        exact hσ x (Subtype.ext h.symm)
      rcases canonicalCommonImage_explicitOppositeCut_or_twoCommon
          hloop hjk hkl x.1 (σ x).1 hxne (Q x) (hQ x).1 (hQ x).2 with
        hcut | hs
      · exact hcut
      · exact False.elim (hsquare ⟨x, hs⟩)
    · exact symmDiffFold_endpointCancellation
        (fun x => rowClass m (Q x).1.1 0)
        (fun x => rowClass m x.1.1.1 0) σ


theorem canonicalFixedPointFreeCollisionPerm_cutBoundaryParity_or_square
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (σ : Equiv.Perm ↑S) (hσ : ∀ x, σ x ≠ x)
    (Q : ↑S -> rightMaskFiber ends m j k l zero p)
    (hQ : ∀ x,
      Q x ∈ canonicalMaskRightImages ends m j k l zero p x.1 ∧
      Q x ∈ canonicalMaskRightImages ends m j k l zero p (σ x).1) :
    (∃ x, CanonicalTightTwoRowCollision
      ends m j k l zero p x.1 (σ x).1) ∨
      ((∀ x, CanonicalRowSupportRootComponentCut ends m k zero
        (canonicalCollisionOppositeRow
          m (Q x).1.1 x.1.1.1 (σ x).1.1.1)) ∧
        StatMech.Sharpness.RandomCurrent.sources ends
          (symmDiffFold Finset.univ (fun x =>
            canonicalCollisionOppositeRow
              m (Q x).1.1 x.1.1.1 (σ x).1.1.1)) =
          if (Finset.univ : Finset ↑S).card % 2 = 0 then ∅
          else {j, k} ∆ {k, l}) := by
  rcases canonicalFixedPointFreeCollisionPerm_explicitCuts_or_square
      hloop hjk hkl S σ hσ Q hQ with hsquare | ⟨hcuts, hfold⟩
  · exact Or.inl hsquare
  · right
    refine ⟨hcuts, ?_⟩
    rw [hfold]
    exact sources_symmDiffFold_rightMaskRows
      ends m j k l zero p Finset.univ Q


theorem canonicalCollisionIndexPerm_cutBoundaryParity_or_square
    {A : Type*} [Fintype A]
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (σ : Equiv.Perm A)
    (X : A -> leftMaskFiber ends m j k l zero p)
    (hX : ∀ x, X x ≠ X (σ x))
    (Q : A -> rightMaskFiber ends m j k l zero p)
    (hQ : ∀ x,
      Q x ∈ canonicalMaskRightImages ends m j k l zero p (X x) ∧
      Q x ∈ canonicalMaskRightImages ends m j k l zero p (X (σ x))) :
    (∃ x, CanonicalTightTwoRowCollision
      ends m j k l zero p (X x) (X (σ x))) ∨
      ((∀ x, CanonicalRowSupportRootComponentCut ends m k zero
        (canonicalCollisionOppositeRow
          m (Q x).1.1 (X x).1.1 (X (σ x)).1.1)) ∧
        StatMech.Sharpness.RandomCurrent.sources ends
          (symmDiffFold Finset.univ (fun x =>
            canonicalCollisionOppositeRow
              m (Q x).1.1 (X x).1.1 (X (σ x)).1.1)) =
          if (Finset.univ : Finset A).card % 2 = 0 then ∅
          else {j, k} ∆ {k, l}) := by
  classical
  by_cases hsquare : ∃ x, CanonicalTightTwoRowCollision
      ends m j k l zero p (X x) (X (σ x))
  · exact Or.inl hsquare
  · right
    have hcuts : ∀ x, CanonicalRowSupportRootComponentCut ends m k zero
        (canonicalCollisionOppositeRow
          m (Q x).1.1 (X x).1.1 (X (σ x)).1.1) := by
      intro x
      rcases canonicalCommonImage_explicitOppositeCut_or_twoCommon
          hloop hjk hkl (X x) (X (σ x)) (hX x)
          (Q x) (hQ x).1 (hQ x).2 with hcut | hs
      · exact hcut
      · exact False.elim (hsquare ⟨x, hs⟩)
    refine ⟨hcuts, ?_⟩
    have hfold : symmDiffFold Finset.univ (fun x =>
          canonicalCollisionOppositeRow
            m (Q x).1.1 (X x).1.1 (X (σ x)).1.1) =
        symmDiffFold Finset.univ
          (fun x => rowClass m (Q x).1.1 0) := by
      exact symmDiffFold_endpointCancellation
        (fun x => rowClass m (Q x).1.1 0)
        (fun x => rowClass m (X x).1.1 0) σ
    rw [hfold]
    exact sources_symmDiffFold_rightMaskRows
      ends m j k l zero p Finset.univ Q

end StatMech.GrahamGHS.FourColor
