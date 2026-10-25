/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorAdmissibleRepair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorInvariantMasks
import Instance.StatisticalMechanics.Code.FrontierA.GrahamFourColorAdmissibleRepair
open Finset
open Classical
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {ι W : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype W] [DecidableEq W]


theorem leftFiber_card_eq_sum_maskFibers
    (ends : ι -> Sym2 W) (m : Finset ι) (j k l zero : W) :
    Fintype.card (leftFiber ends m {j, k} {k, l} k zero) =
      ∑ p : Finset ι × Finset ι,
        Fintype.card (leftMaskFiber ends m j k l zero p) := by
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr
    (Equiv.sigmaFiberEquiv
      (fun c : leftFiber ends m {j, k} {k, l} k zero =>
        fourColorMaskProfile m c.1)).symm

theorem rightFiber_card_eq_sum_maskFibers
    (ends : ι -> Sym2 W) (m : Finset ι) (j k l zero : W) :
    Fintype.card (rightFiber ends m {j, k} {k, l} k zero) =
      ∑ p : Finset ι × Finset ι,
        Fintype.card (rightMaskFiber ends m j k l zero p) := by
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr
    (Equiv.sigmaFiberEquiv
      (fun c : rightFiber ends m {j, k} {k, l} k zero =>
        fourColorMaskProfile m c.1)).symm


theorem GrahamFiberMinor_of_maskwise
    (ends : ι -> Sym2 W) (m : Finset ι) (j k l zero : W)
    (hmask : ∀ p : Finset ι × Finset ι,
      Fintype.card (leftMaskFiber ends m j k l zero p) <=
        Fintype.card (rightMaskFiber ends m j k l zero p)) :
    GrahamFiberMinor ends m j k l zero := by
  rw [GrahamFiberMinor, leftFiber_card_eq_sum_maskFibers,
    rightFiber_card_eq_sum_maskFibers]
  exact Finset.sum_le_sum fun p _ => hmask p


theorem rightMaskFiber_nonempty_of_left
    {ends : ι -> Sym2 W} {m : Finset ι} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset ι × Finset ι)
    (c : leftMaskFiber ends m j k l zero p) :
    Nonempty (rightMaskFiber ends m j k l zero p) := by
  let X := canonicalMiddleTransfer ends m c.1.1 k zero
  let Y := canonicalOuterTransfer ends m c.1.1 k zero
  let d := balancedSwap m X Y c.1.1
  have hv := canonicalTransfers_valid hloop hjk hkl c.1.2
  have hdisc := canonicalBalancedSwap_disconnects
    hloop hjk hkl hk0 c.1.2
  have hd : RightPattern ends m {j, k} {k, l} k zero d :=
    rightPattern_of_balancedTransfer c.1.2 hv.1 hv.2.1
      hv.2.2.1 hv.2.2.2 hdisc
  have hprofile : fourColorMaskProfile m d = p := by
    calc
      fourColorMaskProfile m d = fourColorMaskProfile m c.1.1 := by
        simp [fourColorMaskProfile, d, X, Y,
          middleMask_balancedSwap, outerMask_balancedSwap]
      _ = p := c.2
  exact ⟨⟨⟨d, hd⟩, hprofile⟩⟩

end StatMech.GrahamGHS.FourColor
