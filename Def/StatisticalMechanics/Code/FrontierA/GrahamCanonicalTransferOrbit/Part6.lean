/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferOrbit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorCollisionStableSelector
import Mathlib.Data.Prod.Lex
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferOrbit.Part5
open Finset


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


noncomputable def canonicalOrbitSelectorMaskFiberMap
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    (rho : leftMaskFiber ends m j k l zero p ->
      leftMaskFiber ends m j k l zero p)
    (hdisconnect : ∀ c,
      RowsDisconnect ends m
        (balancedSwap m
          (canonicalMiddleTransfer ends m (rho c).1.1 k zero)
          (canonicalOuterTransfer ends m (rho c).1.1 k zero)
          c.1.1) k zero)
    (c : leftMaskFiber ends m j k l zero p) :
    rightMaskFiber ends m j k l zero p := by
  let X := canonicalMiddleTransfer ends m (rho c).1.1 k zero
  let Y := canonicalOuterTransfer ends m (rho c).1.1 k zero
  let q := balancedSwap m X Y c.1.1
  have hv := canonicalTransfers_valid_on_sameMask
    hloop hjk hkl (rho c) c
  have hq : RightPattern ends m {j, k} {k, l} k zero q :=
    rightPattern_of_balancedTransfer c.1.2 hv.1 hv.2.1
      hv.2.2.1 hv.2.2.2 (hdisconnect c)
  refine ⟨⟨q, hq⟩, ?_⟩
  calc
    fourColorMaskProfile m q = fourColorMaskProfile m c.1.1 :=
      fourColorMaskProfile_balancedSwap m X Y c.1.1
    _ = p := c.2


noncomputable def canonicalOrbitSelectorMaskFiberEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    (rho : leftMaskFiber ends m j k l zero p ->
      leftMaskFiber ends m j k l zero p)
    (hrho : IsCanonicalMaskOrbitSelector ends m j k l zero p rho)
    (hdisconnect : ∀ c,
      RowsDisconnect ends m
        (balancedSwap m
          (canonicalMiddleTransfer ends m (rho c).1.1 k zero)
          (canonicalOuterTransfer ends m (rho c).1.1 k zero)
          c.1.1) k zero) :
    leftMaskFiber ends m j k l zero p ↪
      rightMaskFiber ends m j k l zero p where
  toFun := canonicalOrbitSelectorMaskFiberMap
    ends m j k l zero hloop hjk hkl p rho hdisconnect
  inj' := by
    intro c d hcd
    apply Subtype.ext
    apply Subtype.ext
    have hval :
        balancedSwap m
            (canonicalMiddleTransfer ends m (rho c).1.1 k zero)
            (canonicalOuterTransfer ends m (rho c).1.1 k zero) c.1.1 =
          balancedSwap m
            (canonicalMiddleTransfer ends m (rho d).1.1 k zero)
            (canonicalOuterTransfer ends m (rho d).1.1 k zero) d.1.1 := by
      have := congrArg
        (fun q : rightMaskFiber ends m j k l zero p => q.1.1) hcd
      simpa only [canonicalOrbitSelectorMaskFiberMap] using this
    have hadj : CanonicalMaskTransferAdjacent ends m j k l zero p c d := by
      refine ⟨canonicalOrbitSelectorMaskFiberMap
        ends m j k l zero hloop hjk hkl p rho hdisconnect c,
        rho c, rho d, rfl, ?_⟩
      simpa only [canonicalOrbitSelectorMaskFiberMap] using hval
    have hsame : rho c = rho d :=
      hrho.2 c d (Relation.ReflTransGen.single hadj)
    rw [← hsame] at hval
    have hinv := congrArg
      (balancedSwap m
        (canonicalMiddleTransfer ends m (rho c).1.1 k zero)
        (canonicalOuterTransfer ends m (rho c).1.1 k zero)) hval
    simpa only [balancedSwap_involutive] using hinv


end StatMech.GrahamGHS.FourColor
