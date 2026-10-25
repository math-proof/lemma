/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferPairExpansion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferGF2.Part3
import Def.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferPairExpansion.Part3
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


@[simp] theorem mem_canonicalCoveragePairCandidates_iff
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (r s a b : leftMaskFiber ends m j k l zero p) :
    (a, b) ∈ canonicalCoveragePairCandidates ends m j k l zero p r s ↔
      CanonicalMaskTransferOrbit ends m j k l zero p r a ∧
        CanonicalMaskTransferOrbit ends m j k l zero p r b ∧
        canonicalMaskOrbitCoverageUnion ends m j k l zero p a b =
          canonicalMaskOrbitCoverageUnion ends m j k l zero p r s := by
  classical
  simp [canonicalCoveragePairCandidates]

theorem canonicalCoveragePairCandidates_nonempty
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (r s : leftMaskFiber ends m j k l zero p)
    (hrs : CanonicalMaskTransferOrbit ends m j k l zero p r s) :
    (canonicalCoveragePairCandidates ends m j k l zero p r s).Nonempty := by
  refine ⟨(r, s), ?_⟩
  rw [mem_canonicalCoveragePairCandidates_iff]
  exact ⟨canonicalMaskTransferOrbit_refl ends m j k l zero p r,
    hrs, rfl⟩


theorem canonicalMaskOrbitCoverageUnionClosed_of_pairProgress
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hprogress : CanonicalMaskOrbitCoveragePairProgress
      ends m j k l zero p) :
    CanonicalMaskOrbitCoverageUnionClosed ends m j k l zero p := by
  intro r s hrs
  let S := canonicalCoveragePairCandidates ends m j k l zero p r s
  obtain ⟨ab, habS, habMax⟩ := S.exists_max_image
    (fun ab => canonicalCoveragePairScore ends m k zero ab.1.1.1 ab.2.1.1)
    (canonicalCoveragePairCandidates_nonempty
      ends m j k l zero p r s hrs)
  rcases ab with ⟨a, b⟩
  have hab := (mem_canonicalCoveragePairCandidates_iff
    ends m j k l zero p r s a b).mp habS
  have habOrbit : CanonicalMaskTransferOrbit ends m j k l zero p a b :=
    (canonicalMaskTransferOrbit_symm ends m j k l zero p hab.1).trans hab.2.1
  by_cases ha : canonicalMaskOrbitCoverage ends m j k l zero p a =
      canonicalMaskOrbitCoverageUnion ends m j k l zero p a b
  · exact ⟨a, hab.1, ha.trans hab.2.2⟩
  by_cases hb : canonicalMaskOrbitCoverage ends m j k l zero p b =
      canonicalMaskOrbitCoverageUnion ends m j k l zero p a b
  · exact ⟨b, hab.2.1, hb.trans hab.2.2⟩
  rcases hprogress a b habOrbit ha hb with
    ⟨t, hat, htCoverage⟩ | ⟨c, d, hac, had, hcdUnion, hscore⟩
  · exact ⟨t, hab.1.trans hat, htCoverage.trans hab.2.2⟩
  · have hrc : CanonicalMaskTransferOrbit ends m j k l zero p r c :=
      hab.1.trans hac
    have hrd : CanonicalMaskTransferOrbit ends m j k l zero p r d :=
      hab.1.trans had
    have hcdMem : (c, d) ∈ S := by
      rw [mem_canonicalCoveragePairCandidates_iff]
      exact ⟨hrc, hrd, hcdUnion.trans hab.2.2⟩
    have hle := habMax (c, d) hcdMem
    exact False.elim ((not_lt_of_ge hle) hscore)


theorem canonicalMaskOrbitCoverageUnionClosed_of_pairExpansion
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hexpand : CanonicalMaskOrbitCoveragePairExpansion
      ends m j k l zero p) :
    CanonicalMaskOrbitCoverageUnionClosed ends m j k l zero p :=
  canonicalMaskOrbitCoverageUnionClosed_of_pairProgress
    ends m j k l zero p
      (canonicalMaskOrbitCoveragePairProgress_of_pairExpansion
        ends m j k l zero p hexpand)

end StatMech.GrahamGHS.FourColor
