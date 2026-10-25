/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamRowDataMaskHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamRowDataRepairRelation.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorMaskMatching.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamRowDataMaskHall
open Finset
open Classical


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem rowDataRepairEmbedding_of_maskFiberEmbeddings_related
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (f : MaskFiberEmbeddings ends m j k l zero)
    (d : leftRowData ends m j k l zero) :
    RowDataRepairRelated ends m j k l zero d
      (rowDataRepairEmbedding_of_maskFiberEmbeddings
        ends m j k l zero f d) := by
  rw [rowDataRepairRelated_iff_sameMask]
  let c := rowDataToLeftFiber ends m j k l zero d
  let p := fourColorMaskProfile m c.1
  let q := f p (⟨c, rfl⟩ : leftMaskFiber ends m j k l zero p)
  change fourColorMaskProfile m c.1 =
    fourColorMaskProfile m
      (rowDataToRightFiber ends m j k l zero
        (rightFiberToRowData ends m j k l zero q.1)).1
  rw [rowDataToRightFiber_leftInverse]
  exact q.2.symm


theorem rowDataRepairHall_of_maskFiberEmbeddings
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (f : MaskFiberEmbeddings ends m j k l zero) :
    RowDataRepairHall ends m j k l zero :=
  rowDataRepairHall_of_related_embedding ends m j k l zero
    (rowDataRepairEmbedding_of_maskFiberEmbeddings ends m j k l zero f)
    (rowDataRepairEmbedding_of_maskFiberEmbeddings_related
      ends m j k l zero f)


theorem rowDataRepairHall_of_maskwise
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hmask : forall p : Finset I × Finset I,
      Fintype.card (leftMaskFiber ends m j k l zero p) <=
        Fintype.card (rightMaskFiber ends m j k l zero p)) :
    RowDataRepairHall ends m j k l zero := by
  obtain ⟨f⟩ := (nonempty_maskFiberEmbeddings_iff ends m j k l zero).2 hmask
  exact rowDataRepairHall_of_maskFiberEmbeddings ends m j k l zero f


end StatMech.GrahamGHS.FourColor
