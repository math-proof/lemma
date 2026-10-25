/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferCommonGood.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferOrbit.Part8
import Def.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferCommonGood
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem canonicalTransferWorks_iff_rowSymmDiff
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (r c : leftMaskFiber ends m j k l zero p) :
    CanonicalTransferWorks ends m k zero r.1.1 c.1.1 ↔
      ¬ connK ends
          (rowClass m c.1.1 0 ∆
            canonicalTransferUnion ends m k zero r.1.1) k zero ∧
        ¬ connK ends
          (rowClass m c.1.1 1 ∆
            canonicalTransferUnion ends m k zero r.1.1) k zero := by
  have hv := canonicalTransfers_valid_on_sameMask
    hloop hjk hkl r c
  rw [CanonicalTransferWorks, RowsDisconnect,
    rowClass_balancedSwap_zero hv.1 hv.2.1,
    rowClass_balancedSwap_one hv.1 hv.2.1]
  rfl

theorem canonicalTransferWorks_self
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    {p : Finset I × Finset I}
    (c : leftMaskFiber ends m j k l zero p) :
    CanonicalTransferWorks ends m k zero c.1.1 c.1.1 :=
  canonicalBalancedSwap_disconnects hloop hjk hkl hk0 c.1.2


end StatMech.GrahamGHS.FourColor
