/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferCoverageDirected.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferCommonGood.Part5
import Def.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferCoverageDirected
open Finset


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


@[simp] theorem mem_canonicalMaskOrbitCoverage_iff
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (r d : leftMaskFiber ends m j k l zero p) :
    d ∈ canonicalMaskOrbitCoverage ends m j k l zero p r ↔
      CanonicalMaskTransferOrbit ends m j k l zero p r d ∧
        CanonicalTransferWorks ends m k zero r.1.1 d.1.1 := by
  classical
  simp [canonicalMaskOrbitCoverage]


end StatMech.GrahamGHS.FourColor
