/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTightFamilyCutParity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyRootCollision
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalCollisionSquare
import Def.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyCutParity.Part3
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem canonicalMaskRightTightRootCutCoverageMerge_of_incomparableThird
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hthird : CanonicalMaskRightTightRootCutIncomparableThirdMerge
      ends m j k l zero p) :
    CanonicalMaskRightTightRootCutCoverageMerge
      ends m j k l zero p := by
  intro S hSne htight r hrS c hcS hcut
  by_cases hrc : canonicalMaskRightRestrictedCoverage
      ends m j k l zero p S r ⊆
        canonicalMaskRightRestrictedCoverage ends m j k l zero p S c
  · refine ⟨c, hcS, ?_⟩
    intro d hdS hworks
    rcases hworks with hrd | hcd
    · have hd := hrc ((mem_canonicalMaskRightRestrictedCoverage_iff
          ends m j k l zero p S r d).mpr ⟨hdS, hrd⟩)
      exact ((mem_canonicalMaskRightRestrictedCoverage_iff
        ends m j k l zero p S c d).mp hd).2
    · exact hcd
  · by_cases hcr : canonicalMaskRightRestrictedCoverage
        ends m j k l zero p S c ⊆
          canonicalMaskRightRestrictedCoverage ends m j k l zero p S r
    · refine ⟨r, hrS, ?_⟩
      intro d hdS hworks
      rcases hworks with hrd | hcd
      · exact hrd
      · have hd := hcr ((mem_canonicalMaskRightRestrictedCoverage_iff
            ends m j k l zero p S c d).mpr ⟨hdS, hcd⟩)
        exact ((mem_canonicalMaskRightRestrictedCoverage_iff
          ends m j k l zero p S r d).mp hd).2
    · exact hthird S hSne htight r hrS c hcS hcut hrc hcr


theorem canonicalMaskRightHall_of_tightRootCutIncomparableThird
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (hthird : CanonicalMaskRightTightRootCutIncomparableThirdMerge
      ends m j k l zero p) :
    CanonicalMaskRightHall ends m j k l zero p :=
  canonicalMaskRightHall_of_tightRootCutCoverageMerge
    ends m j k l zero hloop hjk hkl hk0 p
      (canonicalMaskRightTightRootCutCoverageMerge_of_incomparableThird
        ends m j k l zero p hthird)


theorem exists_restrictedCoverage_exclusiveWitnesses_of_incomparable
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (r c : leftMaskFiber ends m j k l zero p)
    (hrc : ¬ canonicalMaskRightRestrictedCoverage
        ends m j k l zero p S r ⊆
      canonicalMaskRightRestrictedCoverage ends m j k l zero p S c)
    (hcr : ¬ canonicalMaskRightRestrictedCoverage
        ends m j k l zero p S c ⊆
      canonicalMaskRightRestrictedCoverage ends m j k l zero p S r) :
    (∃ d ∈ S,
      CanonicalTransferWorks ends m k zero r.1.1 d.1.1 ∧
      ¬ CanonicalTransferWorks ends m k zero c.1.1 d.1.1) ∧
    ∃ e ∈ S,
      CanonicalTransferWorks ends m k zero c.1.1 e.1.1 ∧
      ¬ CanonicalTransferWorks ends m k zero r.1.1 e.1.1 := by
  obtain ⟨d, hdR, hdC⟩ := Finset.not_subset.mp hrc
  obtain ⟨e, heC, heR⟩ := Finset.not_subset.mp hcr
  have hdR' := (mem_canonicalMaskRightRestrictedCoverage_iff
    ends m j k l zero p S r d).mp hdR
  have heC' := (mem_canonicalMaskRightRestrictedCoverage_iff
    ends m j k l zero p S c e).mp heC
  refine ⟨⟨d, hdR'.1, hdR'.2, ?_⟩, ⟨e, heC'.1, heC'.2, ?_⟩⟩
  · intro hcd
    exact hdC ((mem_canonicalMaskRightRestrictedCoverage_iff
      ends m j k l zero p S c d).mpr ⟨hdR'.1, hcd⟩)
  · intro hre
    exact heR ((mem_canonicalMaskRightRestrictedCoverage_iff
      ends m j k l zero p S r e).mpr ⟨heC'.1, hre⟩)

set_option maxHeartbeats 1000000 in


theorem restrictedExclusiveWitness_quadrangleExchange_or_badCertificate
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (r c d : leftMaskFiber ends m j k l zero p)
    (hrcOrbit : CanonicalMaskTransferOrbit ends m j k l zero p r c)
    (hrdOrbit : CanonicalMaskTransferOrbit ends m j k l zero p r d)
    (hrd : CanonicalTransferWorks ends m k zero r.1.1 d.1.1)
    (hcd : ¬ CanonicalTransferWorks ends m k zero c.1.1 d.1.1) :
    (∃ t : leftMaskFiber ends m j k l zero p,
      t ∈ canonicalMaskOrbitCoverage ends m j k l zero p c ∧
      t ∉ canonicalMaskOrbitCoverage ends m j k l zero p r) ∨
      (d ∈ canonicalCoverageExclusiveBadQuadrangles
          ends m j k l zero p r c ∧
        CanonicalCoverageExclusiveBoundaryCertificate
          ends m j k l zero p r c d) := by
  have hdR : d ∈ canonicalMaskOrbitCoverage
      ends m j k l zero p r :=
    (mem_canonicalMaskOrbitCoverage_iff
      ends m j k l zero p r d).mpr ⟨hrdOrbit, hrd⟩
  have hdNotC : d ∉ canonicalMaskOrbitCoverage
      ends m j k l zero p c := by
    intro hdC
    exact hcd ((mem_canonicalMaskOrbitCoverage_iff
      ends m j k l zero p c d).mp hdC).2
  by_cases hdisc : RowsDisconnect ends m
      (canonicalQuadrangleCompletion ends m k zero
        r.1.1 c.1.1 d.1.1) k zero
  · let t := canonicalQuadrangleCompletionMemOfDisconnects
      ends m j k l zero hloop hjk hkl p r c d hdisc
    have ht := quadrangleCompletion_mem_coverage_sdiff
      hloop hjk hkl r c d hrcOrbit hdR hdNotC hdisc
    exact Or.inl ⟨t, ht.1, ht.2⟩
  · have hdBad : d ∈ canonicalCoverageExclusiveBadQuadrangles
        ends m j k l zero p r c := by
      rw [mem_canonicalCoverageExclusiveBadQuadrangles_iff]
      exact ⟨hdR, hdNotC, hdisc⟩
    exact Or.inr ⟨hdBad,
      canonicalCoverageExclusiveBadQuadrangle_boundaryCertificate
        hloop hjk hkl r c d hrcOrbit hdBad⟩


theorem canonicalCoverageExclusiveBoundaryCertificate_zeroRootNormalized
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {p : Finset I × Finset I}
    (a b c : leftMaskFiber ends m j k l zero p)
    (hcert : CanonicalCoverageExclusiveBoundaryCertificate
      ends m j k l zero p a b c) :
    let d := canonicalQuadrangleCompletion ends m k zero
      a.1.1 b.1.1 c.1.1
    ((StatMech.Sharpness.RandomCurrent.connK
          ends (rowClass m d 0) k zero ∧
        StatMech.Sharpness.RandomCurrent.sources
          ends (edgeComponent ends (rowClass m d 0) zero) = {j, k} ∧
        StatMech.Sharpness.RandomCurrent.sources ends (rowClass m d 0 \
          edgeComponent ends (rowClass m d 0) zero) = ∅ ∧
        Disjoint (canonicalTransferUnion ends m k zero d)
          (rowClass m d 0 \ edgeComponent ends (rowClass m d 0) zero)) ∨
      (StatMech.Sharpness.RandomCurrent.connK
          ends (rowClass m d 1) k zero ∧
        StatMech.Sharpness.RandomCurrent.sources
          ends (edgeComponent ends (rowClass m d 1) zero) = {k, l} ∧
        StatMech.Sharpness.RandomCurrent.sources ends (rowClass m d 1 \
          edgeComponent ends (rowClass m d 1) zero) = ∅ ∧
        Disjoint (canonicalTransferUnion ends m k zero d)
          (rowClass m d 1 \ edgeComponent ends (rowClass m d 1) zero))) := by
  dsimp only
  rcases hcert with hzero | hone
  · exact Or.inl hzero
  · right
    have heq : edgeComponent ends
        (rowClass m
          (canonicalQuadrangleCompletion ends m k zero
            a.1.1 b.1.1 c.1.1) 1) k =
      edgeComponent ends
        (rowClass m
          (canonicalQuadrangleCompletion ends m k zero
            a.1.1 b.1.1 c.1.1) 1) zero :=
      edgeComponent_eq_of_conn ends _ k zero hone.1
    rw [← heq]
    exact hone


theorem canonicalCoverageExclusiveBoundaryCertificate_component_ne_complement
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {p : Finset I × Finset I}
    (a b c : leftMaskFiber ends m j k l zero p)
    (hcert : CanonicalCoverageExclusiveBoundaryCertificate
      ends m j k l zero p a b c) :
    let d := canonicalQuadrangleCompletion ends m k zero
      a.1.1 b.1.1 c.1.1
    ((StatMech.Sharpness.RandomCurrent.connK
          ends (rowClass m d 0) k zero ∧
        edgeComponent ends (rowClass m d 0) zero ≠
          rowClass m d 0 \ edgeComponent ends (rowClass m d 0) zero) ∨
      (StatMech.Sharpness.RandomCurrent.connK
          ends (rowClass m d 1) k zero ∧
        edgeComponent ends (rowClass m d 1) zero ≠
          rowClass m d 1 \ edgeComponent ends (rowClass m d 1) zero)) := by
  dsimp only
  rcases canonicalCoverageExclusiveBoundaryCertificate_zeroRootNormalized
      a b c hcert with hzero | hone
  · left
    refine ⟨hzero.1, ?_⟩
    intro heq
    have hs := congrArg (StatMech.Sharpness.RandomCurrent.sources ends) heq
    rw [hzero.2.1, hzero.2.2.1] at hs
    have hj : j ∈ ({j, k} : Finset W) := by simp
    rw [hs] at hj
    simp at hj
  · right
    refine ⟨hone.1, ?_⟩
    intro heq
    have hs := congrArg (StatMech.Sharpness.RandomCurrent.sources ends) heq
    rw [hone.2.1, hone.2.2.1] at hs
    have hk : k ∈ ({k, l} : Finset W) := by simp
    rw [hs] at hk
    simp at hk


end StatMech.GrahamGHS.FourColor
