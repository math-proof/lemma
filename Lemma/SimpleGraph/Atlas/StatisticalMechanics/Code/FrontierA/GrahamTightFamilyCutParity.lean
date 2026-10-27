import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyCutParity.Part5
open Finset StatMech StatMech.GrahamGHS StatMech.GrahamGHS.FourColor


/--
[canonicalCollisionOppositeRow_consecutive_symmDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTightFamilyCutParity.lean)
-/
@[path]
private lemma canonicalCollisionOppositeRow_consecutive_symmDiff_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
-- given
  (q r c d e : ↑m -> Fin 4) :
-- imply
  canonicalCollisionOppositeRow m q c d ∆ canonicalCollisionOppositeRow m r d e = rowClass m q 0 ∆ rowClass m r 0 ∆ rowClass m c 0 ∆ rowClass m e 0 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalCollisionOppositeRow_consecutive_symmDiff m q r c d e

/--
[sources_consecutive_canonicalCollisionOppositeRows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTightFamilyCutParity.lean)
-/
@[path]
private lemma sources_consecutive_canonicalCollisionOppositeRows_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {q r : rightMaskFiber ends m j k l zero p}
  {c d e : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W) :
-- imply
  StatMech.Sharpness.RandomCurrent.sources ends (canonicalCollisionOppositeRow m q.1.1 c.1.1 d.1.1 ∆ canonicalCollisionOppositeRow m r.1.1 d.1.1 e.1.1) = ∅ := by
-- proof
  apply StatMech.GrahamGHS.FourColor.sources_consecutive_canonicalCollisionOppositeRows ends m j k l zero p q r c d e

/--
[canonicalOpposingRootCutsAtRight_crossTranslatedRows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTightFamilyCutParity.lean)
-/
@[path]
private lemma canonicalOpposingRootCutsAtRight_crossTranslatedRows_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c d : leftMaskFiber ends m j k l zero p}
  {q : rightMaskFiber ends m j k l zero p}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hcuts : CanonicalOpposingRootCutsAtRight ends m j k l zero p c d q) :
-- imply
  ∃ a b : leftMaskFiber ends m j k l zero p, canonicalCollisionOppositeRow m q.1.1 c.1.1 d.1.1 = canonicalTranslatedRow ends m k zero b.1.1 c.1.1 ∧ canonicalCollisionOppositeRow m q.1.1 c.1.1 d.1.1 = canonicalTranslatedRow ends m k zero a.1.1 d.1.1 ∧ CanonicalTranslatedRowRootComponentCut ends m k zero b.1.1 c.1.1 ∧ CanonicalTranslatedRowRootComponentCut ends m k zero a.1.1 d.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalOpposingRootCutsAtRight_crossTranslatedRows hloop hjk hkl c d q hcuts

/--
[canonicalCommonImage_opposingAtRight_or_twoCommon](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTightFamilyCutParity.lean)
-/
@[path]
private lemma canonicalCommonImage_opposingAtRight_or_twoCommon_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c d : leftMaskFiber ends m j k l zero p}
  {q : rightMaskFiber ends m j k l zero p}
-- given
  (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hcd : c ≠ d)
  (hqc : q ∈ canonicalMaskRightImages ends m j k l zero p c)
  (hqd : q ∈ canonicalMaskRightImages ends m j k l zero p d) :
-- imply
  CanonicalOpposingRootCutsAtRight ends m j k l zero p c d q ∨ CanonicalTightTwoRowCollision ends m j k l zero p c d := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalCommonImage_opposingAtRight_or_twoCommon hloop hjk hkl c d hcd q hqc hqd

/--
[canonicalSelfImage_owner_rootComponentCut_or_works_twoCommon](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTightFamilyCutParity.lean)
-/
@[path]
private lemma canonicalSelfImage_owner_rootComponentCut_or_works_twoCommon_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c d : leftMaskFiber ends m j k l zero p}
-- given
  (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hcd : c ≠ d)
  (howner : canonicalTransferMapOfWorks ends m j k l zero hloop hjk hkl p c c (canonicalTransferWorks_self hloop hjk hkl hk0 c) ∈ canonicalMaskRightImages ends m j k l zero p d) :
-- imply
  CanonicalTranslatedRowRootComponentCut ends m k zero c.1.1 d.1.1 ∨ (CanonicalTransferWorks ends m k zero c.1.1 d.1.1 ∧ CanonicalTightTwoRowCollision ends m j k l zero p c d) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalSelfImage_owner_rootComponentCut_or_works_twoCommon hloop hjk hkl hk0 c d hcd howner

/--
[canonicalSelfImage_owner_rootComponentCut_or_twoCommon](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTightFamilyCutParity.lean)
-/
@[path]
private lemma canonicalSelfImage_owner_rootComponentCut_or_twoCommon_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c d : leftMaskFiber ends m j k l zero p}
-- given
  (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hcd : c ≠ d)
  (howner : canonicalTransferMapOfWorks ends m j k l zero hloop hjk hkl p c c (canonicalTransferWorks_self hloop hjk hkl hk0 c) ∈ canonicalMaskRightImages ends m j k l zero p d) :
-- imply
  CanonicalTranslatedRowRootComponentCut ends m k zero c.1.1 d.1.1 ∨ CanonicalTightTwoRowCollision ends m j k l zero p c d := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalSelfImage_owner_rootComponentCut_or_twoCommon hloop hjk hkl hk0 c d hcd howner

/--
[canonicalReferenceImage_owner_rootComponentCut_or_works_twoCommon](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTightFamilyCutParity.lean)
-/
@[path]
private lemma canonicalReferenceImage_owner_rootComponentCut_or_works_twoCommon_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {r c d : leftMaskFiber ends m j k l zero p}
-- given
  (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hrc : CanonicalTransferWorks ends m k zero r.1.1 c.1.1)
  (hcd : c ≠ d)
  (howner : canonicalTransferMapOfWorks ends m j k l zero hloop hjk hkl p r c hrc ∈ canonicalMaskRightImages ends m j k l zero p d) :
-- imply
  CanonicalTranslatedRowRootComponentCut ends m k zero r.1.1 d.1.1 ∨ (CanonicalTransferWorks ends m k zero r.1.1 d.1.1 ∧ CanonicalTightTwoRowCollision ends m j k l zero p c d) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalReferenceImage_owner_rootComponentCut_or_works_twoCommon hloop hjk hkl r c d hrc hcd howner

/--
[tightFamily_referenceImage_internalCut_or_coverageGrowth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTightFamilyCutParity.lean)
-/
@[path]
private lemma tightFamily_referenceImage_internalCut_or_coverageGrowth_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  [DecidableEq (leftMaskFiber ends m j k l zero p)]
  {S : Finset (leftMaskFiber ends m j k l zero p)}
  {r c : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hrS : r ∈ S)
  (hcS : c ∈ S)
  (herase : canonicalMaskRightNeighborhood ends m j k l zero p (S.erase c) = canonicalMaskRightNeighborhood ends m j k l zero p S)
  (hrc : CanonicalTransferWorks ends m k zero r.1.1 c.1.1) :
-- imply
  ∃ d ∈ S, d ≠ c ∧ (CanonicalTranslatedRowRootComponentCut ends m k zero r.1.1 d.1.1 ∨ (CanonicalTransferWorks ends m k zero r.1.1 d.1.1 ∧ CanonicalTightTwoRowCollision ends m j k l zero p c d)) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.tightFamily_referenceImage_internalCut_or_coverageGrowth ends m j k l zero hloop hjk hkl p S r c hrS hcS herase hrc

/--
[tightFamily_referenceCoverageGrowth_of_no_internalCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTightFamilyCutParity.lean)
-/
@[path]
private lemma tightFamily_referenceCoverageGrowth_of_no_internalCut_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  [DecidableEq (leftMaskFiber ends m j k l zero p)]
  {S : Finset (leftMaskFiber ends m j k l zero p)}
  {r c : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hrS : r ∈ S)
  (hcS : c ∈ S)
  (herase : canonicalMaskRightNeighborhood ends m j k l zero p (S.erase c) = canonicalMaskRightNeighborhood ends m j k l zero p S)
  (hrc : CanonicalTransferWorks ends m k zero r.1.1 c.1.1)
  (hno : ∀ a ∈ S, ∀ b ∈ S, ¬ CanonicalTranslatedRowRootComponentCut ends m k zero a.1.1 b.1.1) :
-- imply
  ∃ d ∈ S, d ≠ c ∧ CanonicalTransferWorks ends m k zero r.1.1 d.1.1 ∧ CanonicalTightTwoRowCollision ends m j k l zero p c d := by
-- proof
  apply StatMech.GrahamGHS.FourColor.tightFamily_referenceCoverageGrowth_of_no_internalCut ends m j k l zero hloop hjk hkl p S r c hrS hcS herase hrc hno

/--
[tightFamily_selfImage_internalCut_or_twoCommon](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTightFamilyCutParity.lean)
-/
@[path]
private lemma tightFamily_selfImage_internalCut_or_twoCommon_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  [DecidableEq (leftMaskFiber ends m j k l zero p)]
  {S : Finset (leftMaskFiber ends m j k l zero p)}
  {c : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hc : c ∈ S)
  (herase : canonicalMaskRightNeighborhood ends m j k l zero p (S.erase c) = canonicalMaskRightNeighborhood ends m j k l zero p S) :
-- imply
  ∃ d ∈ S, d ≠ c ∧ (CanonicalTranslatedRowRootComponentCut ends m k zero c.1.1 d.1.1 ∨ CanonicalTightTwoRowCollision ends m j k l zero p c d) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.tightFamily_selfImage_internalCut_or_twoCommon ends m j k l zero hloop hjk hkl hk0 p S c hc herase

/--
[exists_tightFamily_allSelfImage_internalCut_or_twoCommon_of_not_hall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTightFamilyCutParity.lean)
-/
@[path]
private lemma exists_tightFamily_allSelfImage_internalCut_or_twoCommon_of_not_hall_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  [DecidableEq (leftMaskFiber ends m j k l zero p)]
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hfail : ¬ CanonicalMaskRightHall ends m j k l zero p) :
-- imply
  ∃ S : Finset (leftMaskFiber ends m j k l zero p), S.Nonempty ∧ (canonicalMaskRightNeighborhood ends m j k l zero p S).card + 1 = S.card ∧ ∀ c ∈ S, ∃ d ∈ S, d ≠ c ∧ (CanonicalTranslatedRowRootComponentCut ends m k zero c.1.1 d.1.1 ∨ CanonicalTightTwoRowCollision ends m j k l zero p c d) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_tightFamily_allSelfImage_internalCut_or_twoCommon_of_not_hall ends m j k l zero hloop hjk hkl hk0 p hfail

/--
[canonicalMaskRightTightRootCutCoverageMerge_of_comparable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTightFamilyCutParity.lean)
-/
@[path]
private lemma canonicalMaskRightTightRootCutCoverageMerge_of_comparable_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
-- given
  (ends : I -> Sym2 W)
  (hcomp : CanonicalMaskRightTightRootCutCoverageComparable ends m j k l zero p) :
-- imply
  CanonicalMaskRightTightRootCutCoverageMerge ends m j k l zero p := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskRightTightRootCutCoverageMerge_of_comparable ends m j k l zero p hcomp

/--
[canonicalMaskRightHall_of_tightRootCutCoverageComparable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTightFamilyCutParity.lean)
-/
@[path]
private lemma canonicalMaskRightHall_of_tightRootCutCoverageComparable_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  [DecidableEq (leftMaskFiber ends m j k l zero p)]
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hcomp : CanonicalMaskRightTightRootCutCoverageComparable ends m j k l zero p) :
-- imply
  CanonicalMaskRightHall ends m j k l zero p := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskRightHall_of_tightRootCutCoverageComparable ends m j k l zero hloop hjk hkl hk0 p hcomp

/--
[canonicalMaskRightTightRootCutCoverageMerge_of_incomparableThird](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTightFamilyCutParity.lean)
-/
@[path]
private lemma canonicalMaskRightTightRootCutCoverageMerge_of_incomparableThird_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
-- given
  (ends : I -> Sym2 W)
  (hthird : CanonicalMaskRightTightRootCutIncomparableThirdMerge ends m j k l zero p) :
-- imply
  CanonicalMaskRightTightRootCutCoverageMerge ends m j k l zero p := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskRightTightRootCutCoverageMerge_of_incomparableThird ends m j k l zero p hthird

/--
[canonicalMaskRightHall_of_tightRootCutIncomparableThird](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTightFamilyCutParity.lean)
-/
@[path]
private lemma canonicalMaskRightHall_of_tightRootCutIncomparableThird_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  [DecidableEq (leftMaskFiber ends m j k l zero p)]
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hthird : CanonicalMaskRightTightRootCutIncomparableThirdMerge ends m j k l zero p) :
-- imply
  CanonicalMaskRightHall ends m j k l zero p := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskRightHall_of_tightRootCutIncomparableThird ends m j k l zero hloop hjk hkl hk0 p hthird

/--
[exists_restrictedCoverage_exclusiveWitnesses_of_incomparable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTightFamilyCutParity.lean)
-/
@[path]
private lemma exists_restrictedCoverage_exclusiveWitnesses_of_incomparable_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {S : Finset (leftMaskFiber ends m j k l zero p)}
  {r c : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (hrc : ¬ canonicalMaskRightRestrictedCoverage ends m j k l zero p S r ⊆ canonicalMaskRightRestrictedCoverage ends m j k l zero p S c)
  (hcr : ¬ canonicalMaskRightRestrictedCoverage ends m j k l zero p S c ⊆ canonicalMaskRightRestrictedCoverage ends m j k l zero p S r) :
-- imply
  (∃ d ∈ S, CanonicalTransferWorks ends m k zero r.1.1 d.1.1 ∧ ¬ CanonicalTransferWorks ends m k zero c.1.1 d.1.1) ∧ ∃ e ∈ S, CanonicalTransferWorks ends m k zero c.1.1 e.1.1 ∧ ¬ CanonicalTransferWorks ends m k zero r.1.1 e.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_restrictedCoverage_exclusiveWitnesses_of_incomparable ends m j k l zero p S r c hrc hcr

/--
[restrictedExclusiveWitness_quadrangleExchange_or_badCertificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTightFamilyCutParity.lean)
-/
@[path]
private lemma restrictedExclusiveWitness_quadrangleExchange_or_badCertificate_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {r c d : leftMaskFiber ends m j k l zero p}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hrcOrbit : CanonicalMaskTransferOrbit ends m j k l zero p r c)
  (hrdOrbit : CanonicalMaskTransferOrbit ends m j k l zero p r d)
  (hrd : CanonicalTransferWorks ends m k zero r.1.1 d.1.1)
  (hcd : ¬ CanonicalTransferWorks ends m k zero c.1.1 d.1.1) :
-- imply
  (∃ t : leftMaskFiber ends m j k l zero p, t ∈ canonicalMaskOrbitCoverage ends m j k l zero p c ∧ t ∉ canonicalMaskOrbitCoverage ends m j k l zero p r) ∨ (d ∈ canonicalCoverageExclusiveBadQuadrangles ends m j k l zero p r c ∧ CanonicalCoverageExclusiveBoundaryCertificate ends m j k l zero p r c d) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.restrictedExclusiveWitness_quadrangleExchange_or_badCertificate hloop hjk hkl r c d hrcOrbit hrdOrbit hrd hcd

/--
[canonicalCoverageExclusiveBoundaryCertificate_zeroRootNormalized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTightFamilyCutParity.lean)
-/
@[path]
private lemma canonicalCoverageExclusiveBoundaryCertificate_zeroRootNormalized_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {a b c : leftMaskFiber ends m j k l zero p}
-- given
  (hcert : CanonicalCoverageExclusiveBoundaryCertificate ends m j k l zero p a b c) :
-- imply
  let d := canonicalQuadrangleCompletion ends m k zero a.1.1 b.1.1 c.1.1 ((StatMech.Sharpness.RandomCurrent.connK ends (rowClass m d 0) k zero ∧ StatMech.Sharpness.RandomCurrent.sources ends (edgeComponent ends (rowClass m d 0) zero) = {j, k} ∧ StatMech.Sharpness.RandomCurrent.sources ends (rowClass m d 0 \ edgeComponent ends (rowClass m d 0) zero) = ∅ ∧ Disjoint (canonicalTransferUnion ends m k zero d) (rowClass m d 0 \ edgeComponent ends (rowClass m d 0) zero)) ∨ (StatMech.Sharpness.RandomCurrent.connK ends (rowClass m d 1) k zero ∧ StatMech.Sharpness.RandomCurrent.sources ends (edgeComponent ends (rowClass m d 1) zero) = {k, l} ∧ StatMech.Sharpness.RandomCurrent.sources ends (rowClass m d 1 \ edgeComponent ends (rowClass m d 1) zero) = ∅ ∧ Disjoint (canonicalTransferUnion ends m k zero d) (rowClass m d 1 \ edgeComponent ends (rowClass m d 1) zero))) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalCoverageExclusiveBoundaryCertificate_zeroRootNormalized a b c hcert

/--
[canonicalCoverageExclusiveBoundaryCertificate_component_ne_complement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTightFamilyCutParity.lean)
-/
@[path]
private lemma canonicalCoverageExclusiveBoundaryCertificate_component_ne_complement_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {a b c : leftMaskFiber ends m j k l zero p}
-- given
  (hcert : CanonicalCoverageExclusiveBoundaryCertificate ends m j k l zero p a b c) :
-- imply
  let d := canonicalQuadrangleCompletion ends m k zero a.1.1 b.1.1 c.1.1 ((StatMech.Sharpness.RandomCurrent.connK ends (rowClass m d 0) k zero ∧ edgeComponent ends (rowClass m d 0) zero ≠ rowClass m d 0 \ edgeComponent ends (rowClass m d 0) zero) ∨ (StatMech.Sharpness.RandomCurrent.connK ends (rowClass m d 1) k zero ∧ edgeComponent ends (rowClass m d 1) zero ≠ rowClass m d 1 \ edgeComponent ends (rowClass m d 1) zero)) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalCoverageExclusiveBoundaryCertificate_component_ne_complement a b c hcert

/--
[exists_normalizedBoundaryRow_of_exclusiveBoundaryCertificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTightFamilyCutParity.lean)
-/
@[path]
private lemma exists_normalizedBoundaryRow_of_exclusiveBoundaryCertificate_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {a b c : leftMaskFiber ends m j k l zero p}
-- given
  (hcert : CanonicalCoverageExclusiveBoundaryCertificate ends m j k l zero p a b c) :
-- imply
  ∃ rho : Fin 2, CanonicalCoverageNormalizedBoundaryRow ends m j k l zero (canonicalQuadrangleCompletion ends m k zero a.1.1 b.1.1 c.1.1) rho := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_normalizedBoundaryRow_of_exclusiveBoundaryCertificate a b c hcert

/--
[normalizedBoundaryRow_component_ne_other_complement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTightFamilyCutParity.lean)
-/
@[path]
private lemma normalizedBoundaryRow_component_ne_other_complement_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {rho sigma : Fin 2}
-- given
  (ends : I -> Sym2 W)
  (d e : ↑m -> Fin 4)
  (hd : CanonicalCoverageNormalizedBoundaryRow ends m j k l zero d rho)
  (he : CanonicalCoverageNormalizedBoundaryRow ends m j k l zero e sigma) :
-- imply
  edgeComponent ends (rowClass m d rho) zero ≠ rowClass m e sigma \ edgeComponent ends (rowClass m e sigma) zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.normalizedBoundaryRow_component_ne_other_complement ends m j k l zero d e rho sigma hd he

/--
[opposingQuadrangle_rowClass_eq_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTightFamilyCutParity.lean)
-/
@[path]
private lemma opposingQuadrangle_rowClass_eq_iff_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {a b c d : leftMaskFiber ends m j k l zero p}
  {rho : Fin 2}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l) :
-- imply
  rowClass m (canonicalQuadrangleCompletion ends m k zero a.1.1 b.1.1 c.1.1) rho = rowClass m (canonicalQuadrangleCompletion ends m k zero b.1.1 a.1.1 d.1.1) rho ↔ rowClass m c.1.1 rho = rowClass m d.1.1 rho := by
-- proof
  apply StatMech.GrahamGHS.FourColor.opposingQuadrangle_rowClass_eq_iff hloop hjk hkl a b c d rho

/--
[opposingExclusiveBadQuadrangles_rowZero_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTightFamilyCutParity.lean)
-/
@[path]
private lemma opposingExclusiveBadQuadrangles_rowZero_ne_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {r y d : leftMaskFiber ends m j k l zero p}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hy : y ∈ canonicalCoverageExclusiveBadQuadrangles ends m j k l zero p y r)
  (hd : d ∈ canonicalCoverageExclusiveBadQuadrangles ends m j k l zero p r y) :
-- imply
  rowClass m (canonicalQuadrangleCompletion ends m k zero y.1.1 r.1.1 y.1.1) 0 ≠ rowClass m (canonicalQuadrangleCompletion ends m k zero r.1.1 y.1.1 d.1.1) 0 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.opposingExclusiveBadQuadrangles_rowZero_ne hloop hjk hkl r y d hy hd

/--
[incomparableRestrictedCoverage_controlledOwnerDichotomies](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTightFamilyCutParity.lean)
-/
@[path]
private lemma incomparableRestrictedCoverage_controlledOwnerDichotomies_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  [DecidableEq (leftMaskFiber ends m j k l zero p)]
  {S : Finset (leftMaskFiber ends m j k l zero p)}
  {r c : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (herase : ∀ x ∈ S, canonicalMaskRightNeighborhood ends m j k l zero p (S.erase x) = canonicalMaskRightNeighborhood ends m j k l zero p S)
  (hrS : r ∈ S)
  (hcS : c ∈ S)
  (hrc : ¬ canonicalMaskRightRestrictedCoverage ends m j k l zero p S r ⊆ canonicalMaskRightRestrictedCoverage ends m j k l zero p S c)
  (hcr : ¬ canonicalMaskRightRestrictedCoverage ends m j k l zero p S c ⊆ canonicalMaskRightRestrictedCoverage ends m j k l zero p S r) :
-- imply
  ∃ d ∈ S, ∃ e ∈ S, CanonicalTransferWorks ends m k zero r.1.1 d.1.1 ∧ ¬ CanonicalTransferWorks ends m k zero c.1.1 d.1.1 ∧ CanonicalTransferWorks ends m k zero c.1.1 e.1.1 ∧ ¬ CanonicalTransferWorks ends m k zero r.1.1 e.1.1 ∧ (∃ u ∈ S, u ≠ d ∧ (CanonicalTranslatedRowRootComponentCut ends m k zero r.1.1 u.1.1 ∨ (CanonicalTransferWorks ends m k zero r.1.1 u.1.1 ∧ CanonicalTightTwoRowCollision ends m j k l zero p d u))) ∧ ∃ v ∈ S, v ≠ e ∧ (CanonicalTranslatedRowRootComponentCut ends m k zero c.1.1 v.1.1 ∨ (CanonicalTransferWorks ends m k zero c.1.1 v.1.1 ∧ CanonicalTightTwoRowCollision ends m j k l zero p e v)) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.incomparableRestrictedCoverage_controlledOwnerDichotomies ends m j k l zero hloop hjk hkl p S herase r c hrS hcS hrc hcr

/--
[exists_tightFamily_incomparableRootCut_of_not_hall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTightFamilyCutParity.lean)
-/
@[path]
private lemma exists_tightFamily_incomparableRootCut_of_not_hall_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  [DecidableEq (leftMaskFiber ends m j k l zero p)]
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hfail : ¬ CanonicalMaskRightHall ends m j k l zero p) :
-- imply
  ∃ S : Finset (leftMaskFiber ends m j k l zero p), S.Nonempty ∧ (canonicalMaskRightNeighborhood ends m j k l zero p S).card + 1 = S.card ∧ (∀ x ∈ S, canonicalMaskRightNeighborhood ends m j k l zero p (S.erase x) = canonicalMaskRightNeighborhood ends m j k l zero p S) ∧ (∀ x ∈ S, ∀ y ∈ S, CanonicalMaskTransferOrbit ends m j k l zero p x y) ∧ ∃ r ∈ S, ∃ c ∈ S, CanonicalTranslatedRowRootComponentCut ends m k zero r.1.1 c.1.1 ∧ ¬ canonicalMaskRightRestrictedCoverage ends m j k l zero p S r ⊆ canonicalMaskRightRestrictedCoverage ends m j k l zero p S c ∧ ¬ canonicalMaskRightRestrictedCoverage ends m j k l zero p S c ⊆ canonicalMaskRightRestrictedCoverage ends m j k l zero p S r := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_tightFamily_incomparableRootCut_of_not_hall ends m j k l zero hloop hjk hkl hk0 p hfail

/--
[exists_secondCommonImage_iff_canonicalTightTwoRowCollision](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTightFamilyCutParity.lean)
-/
@[path]
private lemma exists_secondCommonImage_iff_canonicalTightTwoRowCollision_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c d : leftMaskFiber ends m j k l zero p}
  {q : rightMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (hqc : q ∈ canonicalMaskRightImages ends m j k l zero p c)
  (hqd : q ∈ canonicalMaskRightImages ends m j k l zero p d) :
-- imply
  (∃ r : rightMaskFiber ends m j k l zero p, r ≠ q ∧ r ∈ canonicalMaskRightImages ends m j k l zero p c ∧ r ∈ canonicalMaskRightImages ends m j k l zero p d) ↔ CanonicalTightTwoRowCollision ends m j k l zero p c d := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_secondCommonImage_iff_canonicalTightTwoRowCollision ends m j k l zero p c d q hqc hqd

/--
[common_canonicalMaskRightImage_eq_of_not_twoRowCollision](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTightFamilyCutParity.lean)
-/
@[path]
private lemma common_canonicalMaskRightImage_eq_of_not_twoRowCollision_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c d : leftMaskFiber ends m j k l zero p}
  {q r : rightMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (hno : ¬ CanonicalTightTwoRowCollision ends m j k l zero p c d)
  (hqc : q ∈ canonicalMaskRightImages ends m j k l zero p c)
  (hqd : q ∈ canonicalMaskRightImages ends m j k l zero p d)
  (hrc : r ∈ canonicalMaskRightImages ends m j k l zero p c)
  (hrd : r ∈ canonicalMaskRightImages ends m j k l zero p d) :
-- imply
  r = q := by
-- proof
  apply StatMech.GrahamGHS.FourColor.common_canonicalMaskRightImage_eq_of_not_twoRowCollision ends m j k l zero p c d hno q r hqc hqd hrc hrd

/--
[canonicalMaskRightAugmentedRootCollision_opposingAtRight_or_reroute](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTightFamilyCutParity.lean)
-/
@[path]
private lemma canonicalMaskRightAugmentedRootCollision_opposingAtRight_or_reroute_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {S : Finset (leftMaskFiber ends m j k l zero p)}
  {c : ↑S}
  {f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S}
  {q : ↑(canonicalMaskRightNeighborhood ends m j k l zero p S)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hf : CanonicalMaskRightAugmentedMatching ends m j k l zero p S c f)
  (hqc : q.1 ∈ canonicalMaskRightImages ends m j k l zero p c.1) :
-- imply
  (∃ d : ↑S, d ≠ c ∧ f d = some q ∧ CanonicalOpposingRootCutsAtRight ends m j k l zero p c.1 d.1 q.1) ∨ ∃ e : ↑S, e ≠ c ∧ ∃ g : canonicalMaskRightAugmentedEquivType ends m j k l zero p S, CanonicalMaskRightAugmentedMatching ends m j k l zero p S e g := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskRightAugmentedRootCollision_opposingAtRight_or_reroute ends m j k l zero hloop hjk hkl p S c f hf q hqc

/--
[canonicalMaskRightAugmentedSelfImage_internalCut_or_reroute](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTightFamilyCutParity.lean)
-/
@[path]
private lemma canonicalMaskRightAugmentedSelfImage_internalCut_or_reroute_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {S : Finset (leftMaskFiber ends m j k l zero p)}
  {c : ↑S}
  {f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hf : CanonicalMaskRightAugmentedMatching ends m j k l zero p S c f) :
-- imply
  (∃ d : ↑S, d ≠ c ∧ CanonicalTranslatedRowRootComponentCut ends m k zero c.1.1.1 d.1.1.1) ∨ ∃ e : ↑S, e ≠ c ∧ ∃ g : canonicalMaskRightAugmentedEquivType ends m j k l zero p S, CanonicalMaskRightAugmentedMatching ends m j k l zero p S e g := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskRightAugmentedSelfImage_internalCut_or_reroute ends m j k l zero hloop hjk hkl hk0 p S c f hf

/--
[canonicalConsecutiveTriple_twoRow_or_chord_or_escape](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTightFamilyCutParity.lean)
-/
@[path]
private lemma canonicalConsecutiveTriple_twoRow_or_chord_or_escape_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  [DecidableEq (leftMaskFiber ends m j k l zero p)]
  {S : Finset (leftMaskFiber ends m j k l zero p)}
  {c d e : leftMaskFiber ends m j k l zero p}
  {q r : rightMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (hproper : ∀ T : Finset (leftMaskFiber ends m j k l zero p), T ⊂ S -> T.card ≤ (canonicalMaskRightNeighborhood ends m j k l zero p T).card)
  (herase : ∀ x ∈ S, canonicalMaskRightNeighborhood ends m j k l zero p (S.erase x) = canonicalMaskRightNeighborhood ends m j k l zero p S)
  (hcd : c ≠ d)
  (hce : c ≠ e)
  (hde : d ≠ e)
  (htriple : ({c, d, e} : Finset (leftMaskFiber ends m j k l zero p)) ⊂ S)
  (hqc : q ∈ canonicalMaskRightImages ends m j k l zero p c)
  (hqd : q ∈ canonicalMaskRightImages ends m j k l zero p d)
  (hrd : r ∈ canonicalMaskRightImages ends m j k l zero p d)
  (hre : r ∈ canonicalMaskRightImages ends m j k l zero p e) :
-- imply
  CanonicalTightTwoRowCollision ends m j k l zero p c d ∨ CanonicalTightTwoRowCollision ends m j k l zero p d e ∨ ∃ x ∈ ({c, d, e} : Finset (leftMaskFiber ends m j k l zero p)), ∃ y ∈ S, y ≠ x ∧ ∃ s : rightMaskFiber ends m j k l zero p, s ≠ q ∧ s ≠ r ∧ s ∈ canonicalMaskRightImages ends m j k l zero p x ∧ s ∈ canonicalMaskRightImages ends m j k l zero p y ∧ ((x = c ∧ y = e) ∨ (x = e ∧ y = c) ∨ y ∉ ({c, d, e} : Finset (leftMaskFiber ends m j k l zero p))) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalConsecutiveTriple_twoRow_or_chord_or_escape ends m j k l zero p S hproper herase c d e hcd hce hde htriple q r hqc hqd hrd hre

/--
[exists_twoRowCollision_of_tight_canonicalMaskRightNeighborhood](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTightFamilyCutParity.lean)
-/
@[path]
private lemma exists_twoRowCollision_of_tight_canonicalMaskRightNeighborhood_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {S : Finset (leftMaskFiber ends m j k l zero p)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (htight : (canonicalMaskRightNeighborhood ends m j k l zero p S).card + 1 = S.card) :
-- imply
  ∃ c ∈ S, ∃ d ∈ S, c ≠ d ∧ CanonicalTightTwoRowCollision ends m j k l zero p c d := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_twoRowCollision_of_tight_canonicalMaskRightNeighborhood ends m j k l zero hloop hjk hkl hk0 p S htight

/--
[canonicalCollisionPerm_twoCycle_twoRow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTightFamilyCutParity.lean)
-/
@[path]
private lemma canonicalCollisionPerm_twoCycle_twoRow_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {S : Finset (leftMaskFiber ends m j k l zero p)}
  {σ : Equiv.Perm ↑S}
  {x : ↑S}
-- given
  (ends : I -> Sym2 W)
  (Q : ↑S -> rightMaskFiber ends m j k l zero p)
  (hQ : ∀ x, Q x ∈ canonicalMaskRightImages ends m j k l zero p x.1 ∧ Q x ∈ canonicalMaskRightImages ends m j k l zero p (σ x).1)
  (hcycle : σ (σ x) = x)
  (hlabels : Q x ≠ Q (σ x)) :
-- imply
  CanonicalTightTwoRowCollision ends m j k l zero p x.1 (σ x).1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalCollisionPerm_twoCycle_twoRow ends m j k l zero p S σ Q hQ x hcycle hlabels

/--
[canonicalCollisionPerm_secondIterate_ne_of_noTwoRow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTightFamilyCutParity.lean)
-/
@[path]
private lemma canonicalCollisionPerm_secondIterate_ne_of_noTwoRow_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {S : Finset (leftMaskFiber ends m j k l zero p)}
  {σ : Equiv.Perm ↑S}
  {x : ↑S}
-- given
  (ends : I -> Sym2 W)
  (Q : ↑S -> rightMaskFiber ends m j k l zero p)
  (hQ : ∀ x, Q x ∈ canonicalMaskRightImages ends m j k l zero p x.1 ∧ Q x ∈ canonicalMaskRightImages ends m j k l zero p (σ x).1)
  (hQinj : Function.Injective Q)
  (hno : ∀ x, ¬ CanonicalTightTwoRowCollision ends m j k l zero p x.1 (σ x).1)
  (hx : σ x ≠ x) :
-- imply
  σ (σ x) ≠ x := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalCollisionPerm_secondIterate_ne_of_noTwoRow ends m j k l zero p S σ Q hQ hQinj hno x hx

/--
[canonicalInjectiveCollisionPerm_opposingCuts_and_no_twoCycles](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTightFamilyCutParity.lean)
-/
@[path]
private lemma canonicalInjectiveCollisionPerm_opposingCuts_and_no_twoCycles_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {S : Finset (leftMaskFiber ends m j k l zero p)}
  {σ : Equiv.Perm ↑S}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hσ : ∀ x, σ x ≠ x)
  (Q : ↑S -> rightMaskFiber ends m j k l zero p)
  (hQ : ∀ x, Q x ∈ canonicalMaskRightImages ends m j k l zero p x.1 ∧ Q x ∈ canonicalMaskRightImages ends m j k l zero p (σ x).1)
  (hQinj : Function.Injective Q)
  (hno : ∀ x, ¬ CanonicalTightTwoRowCollision ends m j k l zero p x.1 (σ x).1) :
-- imply
  (∀ x, CanonicalOpposingRootCutsAtRight ends m j k l zero p x.1 (σ x).1 (Q x)) ∧ ∀ x, σ (σ x) ≠ x := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalInjectiveCollisionPerm_opposingCuts_and_no_twoCycles hloop hjk hkl S σ hσ Q hQ hQinj hno

/--
[canonicalCollisionIndexPerm_opposingAtRight_or_square](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTightFamilyCutParity.lean)
-/
@[path]
private lemma canonicalCollisionIndexPerm_opposingAtRight_or_square_eq
  [Fintype I]
  [DecidableEq I]
  [Fintype A]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {σ : Equiv.Perm A}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (X : A -> leftMaskFiber ends m j k l zero p)
  (hX : ∀ x, X x ≠ X (σ x))
  (Q : A -> rightMaskFiber ends m j k l zero p)
  (hQ : ∀ x, Q x ∈ canonicalMaskRightImages ends m j k l zero p (X x) ∧ Q x ∈ canonicalMaskRightImages ends m j k l zero p (X (σ x))) :
-- imply
  (∃ x, CanonicalTightTwoRowCollision ends m j k l zero p (X x) (X (σ x))) ∨ ∀ x, CanonicalOpposingRootCutsAtRight ends m j k l zero p (X x) (X (σ x)) (Q x) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalCollisionIndexPerm_opposingAtRight_or_square hloop hjk hkl σ X hX Q hQ

/--
[exists_hallFailure_labelledCollisionPerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTightFamilyCutParity.lean)
-/
@[path]
private lemma exists_hallFailure_labelledCollisionPerm_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  [DecidableEq (leftMaskFiber ends m j k l zero p)]
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hfail : ¬ CanonicalMaskRightHall ends m j k l zero p) :
-- imply
  ∃ S : Finset (leftMaskFiber ends m j k l zero p), ∃ σ : Equiv.Perm ↑S, σ ≠ Equiv.refl ↑S ∧ ∀ x : ↑S, σ x ≠ x -> ∃ q : rightMaskFiber ends m j k l zero p, q ∈ canonicalMaskRightImages ends m j k l zero p x.1 ∧ q ∈ canonicalMaskRightImages ends m j k l zero p (σ x).1 ∧ (CanonicalOpposingRootCutsAtRight ends m j k l zero p x.1 (σ x).1 q ∨ CanonicalTightTwoRowCollision ends m j k l zero p x.1 (σ x).1) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_hallFailure_labelledCollisionPerm ends m j k l zero hloop hjk hkl hk0 p hfail

/--
[canonicalCommonImage_explicitOppositeCut_or_twoCommon](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTightFamilyCutParity.lean)
-/
@[path]
private lemma canonicalCommonImage_explicitOppositeCut_or_twoCommon_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c d : leftMaskFiber ends m j k l zero p}
  {q : rightMaskFiber ends m j k l zero p}
-- given
  (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hcd : c ≠ d)
  (hqc : q ∈ canonicalMaskRightImages ends m j k l zero p c)
  (hqd : q ∈ canonicalMaskRightImages ends m j k l zero p d) :
-- imply
  CanonicalRowSupportRootComponentCut ends m k zero (canonicalCollisionOppositeRow m q.1.1 c.1.1 d.1.1) ∨ CanonicalTightTwoRowCollision ends m j k l zero p c d := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalCommonImage_explicitOppositeCut_or_twoCommon hloop hjk hkl c d hcd q hqc hqd

/--
[canonicalFixedPointFreeCollisionPerm_explicitCuts_or_square](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTightFamilyCutParity.lean)
-/
@[path]
private lemma canonicalFixedPointFreeCollisionPerm_explicitCuts_or_square_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {S : Finset (leftMaskFiber ends m j k l zero p)}
  {σ : Equiv.Perm ↑S}
-- given
  (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hσ : ∀ x, σ x ≠ x)
  (Q : ↑S -> rightMaskFiber ends m j k l zero p)
  (hQ : ∀ x, Q x ∈ canonicalMaskRightImages ends m j k l zero p x.1 ∧ Q x ∈ canonicalMaskRightImages ends m j k l zero p (σ x).1) :
-- imply
  (∃ x, CanonicalTightTwoRowCollision ends m j k l zero p x.1 (σ x).1) ∨ ((∀ x, CanonicalRowSupportRootComponentCut ends m k zero (canonicalCollisionOppositeRow m (Q x).1.1 x.1.1.1 (σ x).1.1.1)) ∧ symmDiffFold Finset.univ (fun x => canonicalCollisionOppositeRow m (Q x).1.1 x.1.1.1 (σ x).1.1.1) = symmDiffFold Finset.univ (fun x => rowClass m (Q x).1.1 0)) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalFixedPointFreeCollisionPerm_explicitCuts_or_square hloop hjk hkl S σ hσ Q hQ

/--
[canonicalFixedPointFreeCollisionPerm_cutBoundaryParity_or_square](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTightFamilyCutParity.lean)
-/
@[path]
private lemma canonicalFixedPointFreeCollisionPerm_cutBoundaryParity_or_square_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {S : Finset (leftMaskFiber ends m j k l zero p)}
  {σ : Equiv.Perm ↑S}
-- given
  (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hσ : ∀ x, σ x ≠ x)
  (Q : ↑S -> rightMaskFiber ends m j k l zero p)
  (hQ : ∀ x, Q x ∈ canonicalMaskRightImages ends m j k l zero p x.1 ∧ Q x ∈ canonicalMaskRightImages ends m j k l zero p (σ x).1) :
-- imply
  (∃ x, CanonicalTightTwoRowCollision ends m j k l zero p x.1 (σ x).1) ∨ ((∀ x, CanonicalRowSupportRootComponentCut ends m k zero (canonicalCollisionOppositeRow m (Q x).1.1 x.1.1.1 (σ x).1.1.1)) ∧ StatMech.Sharpness.RandomCurrent.sources ends (symmDiffFold Finset.univ (fun x => canonicalCollisionOppositeRow m (Q x).1.1 x.1.1.1 (σ x).1.1.1)) = if (Finset.univ : Finset ↑S).card % 2 = 0 then ∅ else {j, k} ∆ {k, l}) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalFixedPointFreeCollisionPerm_cutBoundaryParity_or_square hloop hjk hkl S σ hσ Q hQ

/--
[canonicalCollisionIndexPerm_cutBoundaryParity_or_square](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTightFamilyCutParity.lean)
-/
@[path]
private lemma canonicalCollisionIndexPerm_cutBoundaryParity_or_square_eq
  [Fintype I]
  [DecidableEq I]
  [Fintype A]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {σ : Equiv.Perm A}
-- given
  (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (X : A -> leftMaskFiber ends m j k l zero p)
  (hX : ∀ x, X x ≠ X (σ x))
  (Q : A -> rightMaskFiber ends m j k l zero p)
  (hQ : ∀ x, Q x ∈ canonicalMaskRightImages ends m j k l zero p (X x) ∧ Q x ∈ canonicalMaskRightImages ends m j k l zero p (X (σ x))) :
-- imply
  (∃ x, CanonicalTightTwoRowCollision ends m j k l zero p (X x) (X (σ x))) ∨ ((∀ x, CanonicalRowSupportRootComponentCut ends m k zero (canonicalCollisionOppositeRow m (Q x).1.1 (X x).1.1 (X (σ x)).1.1)) ∧ StatMech.Sharpness.RandomCurrent.sources ends (symmDiffFold Finset.univ (fun x => canonicalCollisionOppositeRow m (Q x).1.1 (X x).1.1 (X (σ x)).1.1)) = if (Finset.univ : Finset A).card % 2 = 0 then ∅ else {j, k} ∆ {k, l}) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalCollisionIndexPerm_cutBoundaryParity_or_square hloop hjk hkl σ X hX Q hQ


-- created on 2026-10-23
