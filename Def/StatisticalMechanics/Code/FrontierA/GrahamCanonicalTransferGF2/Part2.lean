/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferGF2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferCoverageJoin.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferGF2.Part2
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


noncomputable def canonicalTransferMapOfWorks
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    (a c : leftMaskFiber ends m j k l zero p)
    (hworks : CanonicalTransferWorks ends m k zero a.1.1 c.1.1) :
    rightMaskFiber ends m j k l zero p := by
  let X := canonicalMiddleTransfer ends m a.1.1 k zero
  let Y := canonicalOuterTransfer ends m a.1.1 k zero
  let q := balancedSwap m X Y c.1.1
  have hv := canonicalTransfers_valid_on_sameMask hloop hjk hkl a c
  have hq : RightPattern ends m {j, k} {k, l} k zero q :=
    rightPattern_of_balancedTransfer c.1.2 hv.1 hv.2.1
      hv.2.2.1 hv.2.2.2 hworks
  refine ⟨⟨q, hq⟩, ?_⟩
  calc
    fourColorMaskProfile m q = fourColorMaskProfile m c.1.1 :=
      fourColorMaskProfile_balancedSwap m X Y c.1.1
    _ = p := c.2


end StatMech.GrahamGHS.FourColor
