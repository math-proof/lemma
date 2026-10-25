/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferComponentCut.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
import Def.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferMatching.Part15
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


@[simp] theorem mem_canonicalMaskRightRestrictedCoverage_iff
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (r c : leftMaskFiber ends m j k l zero p) :
    c ∈ canonicalMaskRightRestrictedCoverage
        ends m j k l zero p S r ↔
      c ∈ S ∧ CanonicalTransferWorks ends m k zero r.1.1 c.1.1 := by
  classical
  simp [canonicalMaskRightRestrictedCoverage]


theorem canonicalMaskRightRestrictedCoverage_eq_inter_orbitCoverage
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (r : leftMaskFiber ends m j k l zero p)
    (horbit : ∀ d ∈ S,
      CanonicalMaskTransferOrbit ends m j k l zero p r d) :
    canonicalMaskRightRestrictedCoverage ends m j k l zero p S r =
      S ∩ canonicalMaskOrbitCoverage ends m j k l zero p r := by
  classical
  ext d
  simp only [mem_canonicalMaskRightRestrictedCoverage_iff,
    Finset.mem_inter, mem_canonicalMaskOrbitCoverage_iff]
  constructor
  · exact fun hd => ⟨hd.1, horbit d hd.1, hd.2⟩
  · exact fun hd => ⟨hd.1, hd.2.2⟩


end StatMech.GrahamGHS.FourColor
