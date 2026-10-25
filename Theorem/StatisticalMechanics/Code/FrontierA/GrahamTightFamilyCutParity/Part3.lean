/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTightFamilyCutParity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyRootCollision
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalCollisionSquare
import Def.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyCutParity.Part2
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem canonicalMaskRightTightRootCutCoverageMerge_of_comparable
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hcomp : CanonicalMaskRightTightRootCutCoverageComparable
      ends m j k l zero p) :
    CanonicalMaskRightTightRootCutCoverageMerge
      ends m j k l zero p := by
  intro S hSne htight r hrS c hcS hcut
  rcases hcomp S hSne htight r hrS c hcS hcut with hrc | hcr
  · refine ⟨c, hcS, ?_⟩
    intro d hdS hworks
    rcases hworks with hrd | hcd
    · have hd := hrc ((mem_canonicalMaskRightRestrictedCoverage_iff
          ends m j k l zero p S r d).mpr ⟨hdS, hrd⟩)
      exact ((mem_canonicalMaskRightRestrictedCoverage_iff
        ends m j k l zero p S c d).mp hd).2
    · exact hcd
  · refine ⟨r, hrS, ?_⟩
    intro d hdS hworks
    rcases hworks with hrd | hcd
    · exact hrd
    · have hd := hcr ((mem_canonicalMaskRightRestrictedCoverage_iff
          ends m j k l zero p S c d).mpr ⟨hdS, hcd⟩)
      exact ((mem_canonicalMaskRightRestrictedCoverage_iff
        ends m j k l zero p S r d).mp hd).2


theorem canonicalMaskRightHall_of_tightRootCutCoverageComparable
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (hcomp : CanonicalMaskRightTightRootCutCoverageComparable
      ends m j k l zero p) :
    CanonicalMaskRightHall ends m j k l zero p :=
  canonicalMaskRightHall_of_tightRootCutCoverageMerge
    ends m j k l zero hloop hjk hkl hk0 p
      (canonicalMaskRightTightRootCutCoverageMerge_of_comparable
        ends m j k l zero p hcomp)


end StatMech.GrahamGHS.FourColor
