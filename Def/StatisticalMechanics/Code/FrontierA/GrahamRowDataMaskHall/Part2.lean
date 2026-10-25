/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamRowDataMaskHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamRowDataRepairRelation.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorMaskMatching.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamRowDataMaskHall
open Finset
open Classical


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


noncomputable def maskFiberEmbeddings_of_related_injection
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (g : leftRowData ends m j k l zero ->
      rightRowData ends m j k l zero)
    (hg : Function.Injective g)
    (hrelated : forall d, RowDataRepairRelated ends m j k l zero d (g d)) :
    MaskFiberEmbeddings ends m j k l zero := by
  intro p
  refine
    { toFun := fun c => ?_
      inj' := ?_ }
  · let d := leftFiberToRowData ends m j k l zero c.1
    let q := rowDataToRightFiber ends m j k l zero (g d)
    refine ⟨q, ?_⟩
    have hmask := (rowDataRepairRelated_iff_sameMask
      ends m j k l zero d (g d)).1 (hrelated d)
    change fourColorMaskProfile m q.1 = p
    calc
      fourColorMaskProfile m q.1 =
          fourColorMaskProfile m
            (rowDataToLeftFiber ends m j k l zero d).1 := hmask.symm
      _ = fourColorMaskProfile m c.1.1 := by
        rw [rowDataToLeftFiber_leftInverse]
      _ = p := c.2
  · intro c d hcd
    apply Subtype.ext
    apply (leftFiberEquivRowData ends m j k l zero).injective
    change leftFiberToRowData ends m j k l zero c.1 =
      leftFiberToRowData ends m j k l zero d.1
    apply hg
    apply rowDataToRightFiber_injective ends m j k l zero
    have hq := congrArg (fun q => q.1.1) hcd
    dsimp only at hq
    exact Subtype.ext hq


end StatMech.GrahamGHS.FourColor
