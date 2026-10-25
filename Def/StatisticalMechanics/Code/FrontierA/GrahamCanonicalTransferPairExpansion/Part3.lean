/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferPairExpansion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferGF2.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferPairExpansion.Part2
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


noncomputable def canonicalCoveragePairCandidates
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (r s : leftMaskFiber ends m j k l zero p) :
    Finset (leftMaskFiber ends m j k l zero p ×
      leftMaskFiber ends m j k l zero p) := by
  classical
  exact Finset.univ.filter fun ab =>
    CanonicalMaskTransferOrbit ends m j k l zero p r ab.1 ∧
      CanonicalMaskTransferOrbit ends m j k l zero p r ab.2 ∧
      canonicalMaskOrbitCoverageUnion ends m j k l zero p ab.1 ab.2 =
        canonicalMaskOrbitCoverageUnion ends m j k l zero p r s

end StatMech.GrahamGHS.FourColor
