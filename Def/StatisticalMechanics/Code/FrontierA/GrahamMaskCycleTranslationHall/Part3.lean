/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskCycleTranslationHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferComponentCut.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskCycleTranslationHall.Part2
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]

open StatMech.Sharpness.RandomCurrent


noncomputable def maskFiberCycleTranslateEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (a : leftMaskFiber ends m j k l zero p)
    (q : rightMaskFiber ends m j k l zero p)
    (hgate : ∀ c : leftMaskFiber ends m j k l zero p,
      RowsDisconnect ends m
        (rightMaskCycleTranslate m a.1.1 c.1.1 q.1.1) k zero) :
    leftMaskFiber ends m j k l zero p ↪
      rightMaskFiber ends m j k l zero p where
  toFun c := rightMaskCycleTranslateMemOfDisconnects
    ends m j k l zero p a c q (hgate c)
  inj' := by
    intro c d hcd
    apply Subtype.ext
    apply Subtype.ext
    have hval := congrArg
      (fun z : rightMaskFiber ends m j k l zero p => z.1.1) hcd
    let A : {
        x : ↑m -> Fin 4 // fourColorMaskProfile m x =
          fourColorMaskProfile m a.1.1} := ⟨c.1.1, c.2.trans a.2.symm⟩
    let B : {
        x : ↑m -> Fin 4 // fourColorMaskProfile m x =
          fourColorMaskProfile m a.1.1} := ⟨d.1.1, d.2.trans a.2.symm⟩
    have hprofileAQ : fourColorMaskProfile m a.1.1 =
        fourColorMaskProfile m q.1.1 := a.2.trans q.2.symm
    have hAB : A = B := rightMaskCycleTranslate_left_injective
      m a.1.1 q.1.1 hprofileAQ (by
        change rightMaskCycleTranslate m a.1.1 c.1.1 q.1.1 =
          rightMaskCycleTranslate m a.1.1 d.1.1 q.1.1
        exact hval)
    exact congrArg (fun z : {
      x : ↑m -> Fin 4 // fourColorMaskProfile m x =
        fourColorMaskProfile m a.1.1} => z.1) hAB


end StatMech.GrahamGHS.FourColor
