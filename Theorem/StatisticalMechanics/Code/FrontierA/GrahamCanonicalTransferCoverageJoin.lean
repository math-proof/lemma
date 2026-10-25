/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferCoverageJoin.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferCoverageDirected.Part3
import Def.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferCoverageJoin
open Finset


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


@[simp] theorem mem_canonicalMaskOrbitCoverageJoinCandidates_iff
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (r s t : leftMaskFiber ends m j k l zero p) :
    t ∈ canonicalMaskOrbitCoverageJoinCandidates ends m j k l zero p r s ↔
      CanonicalMaskTransferOrbit ends m j k l zero p r t ∧
        canonicalMaskOrbitCoverage ends m j k l zero p t =
          canonicalMaskOrbitCoverageUnion ends m j k l zero p r s := by
  classical
  simp [canonicalMaskOrbitCoverageJoinCandidates]

theorem canonicalMaskOrbitCoverageJoinCandidates_nonempty
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hclosed : CanonicalMaskOrbitCoverageUnionClosed
      ends m j k l zero p)
    (r s : leftMaskFiber ends m j k l zero p)
    (hrs : CanonicalMaskTransferOrbit ends m j k l zero p r s) :
    (canonicalMaskOrbitCoverageJoinCandidates
      ends m j k l zero p r s).Nonempty := by
  obtain ⟨t, hrt, ht⟩ := hclosed r s hrs
  refine ⟨t, ?_⟩
  rw [mem_canonicalMaskOrbitCoverageJoinCandidates_iff]
  exact ⟨hrt, ht⟩


end StatMech.GrahamGHS.FourColor
