/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferAmbientQuadrangle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferCoverageExchange.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferAmbientQuadrangle.Part4
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


set_option maxHeartbeats 1000000 in
@[simp] theorem mem_canonicalCoverageExclusiveGoodQuadrangles_iff
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (a b c : leftMaskFiber ends m j k l zero p) :
    c ∈ canonicalCoverageExclusiveGoodQuadrangles
        ends m j k l zero p a b ↔
      c ∈ canonicalMaskOrbitCoverage ends m j k l zero p a ∧
        c ∉ canonicalMaskOrbitCoverage ends m j k l zero p b ∧
        RowsDisconnect ends m
          (canonicalQuadrangleCompletion ends m k zero
            a.1.1 b.1.1 c.1.1) k zero := by
  classical
  simp only [canonicalCoverageExclusiveGoodQuadrangles,
    canonicalCoverageExclusive, Finset.mem_filter, Finset.mem_sdiff]
  tauto

end StatMech.GrahamGHS.FourColor
