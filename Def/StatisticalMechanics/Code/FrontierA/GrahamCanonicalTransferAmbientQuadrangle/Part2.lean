/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferAmbientQuadrangle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferCoverageExchange.Part2
import Instance.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferAmbientQuadrangle
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


def leftMaskFiberToSourceMaskFiber
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    leftMaskFiber ends m j k l zero p ->
      leftSourceMaskFiber ends m j k l zero p := fun c =>
  ⟨c.1.1, ⟨⟨c.1.2.1, c.1.2.2.1, c.1.2.2.2.1,
    c.1.2.2.2.2.1⟩, c.2⟩⟩

end StatMech.GrahamGHS.FourColor
