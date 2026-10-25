/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamRowDataRepairRelation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamComponentExchangeWeightedCounterexample.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorUniformMaskSelector.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamRowDataRepairRelation
open Finset


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


noncomputable def canonicalRightRowData
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (d : leftRowData ends m j k l zero) :
    rightRowData ends m j k l zero := by
  let c := rowDataToLeftFiber ends m j k l zero d
  let X := canonicalMiddleTransfer ends m c.1 k zero
  let Y := canonicalOuterTransfer ends m c.1 k zero
  let q := balancedSwap m X Y c.1
  have hv := canonicalTransfers_valid hloop hjk hkl c.2
  have hdisc := canonicalBalancedSwap_disconnects
    hloop hjk hkl hk0 c.2
  have hq : RightPattern ends m {j, k} {k, l} k zero q :=
    rightPattern_of_balancedTransfer c.2 hv.1 hv.2.1
      hv.2.2.1 hv.2.2.2 hdisc
  exact rightFiberToRowData ends m j k l zero ⟨q, hq⟩


end StatMech.GrahamGHS.FourColor
