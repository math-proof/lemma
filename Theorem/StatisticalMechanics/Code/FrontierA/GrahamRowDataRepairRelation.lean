/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamRowDataRepairRelation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamComponentExchangeWeightedCounterexample.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorUniformMaskSelector.Part4
import Def.StatisticalMechanics.Code.FrontierA.GrahamRowDataRepairRelation
open Finset


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


@[simp] theorem mem_admissibleRightRowRepairs_iff
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (d : leftRowData ends m j k l zero)
    (e : rightRowData ends m j k l zero) :
    e ∈ admissibleRightRowRepairs ends m j k l zero d ↔
      RowDataRepairRelated ends m j k l zero d e := by
  classical
  simp [admissibleRightRowRepairs]


theorem rowDataRepairRelated_iff_sameMask
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (d : leftRowData ends m j k l zero)
    (e : rightRowData ends m j k l zero) :
    RowDataRepairRelated ends m j k l zero d e ↔
      fourColorMaskProfile m
          (rowDataToLeftFiber ends m j k l zero d).1 =
        fourColorMaskProfile m
          (rowDataToRightFiber ends m j k l zero e).1 := by
  let c := (rowDataToLeftFiber ends m j k l zero d).1
  let q := (rowDataToRightFiber ends m j k l zero e).1
  have hc := (rowDataToLeftFiber ends m j k l zero d).2
  have hq := (rowDataToRightFiber ends m j k l zero e).2
  change (∃ X Y : Finset I,
      X ⊆ middleMask m c ∧
        Y ⊆ outerMask m c ∧
        sources ends X = {k, l} ∧
        sources ends Y = ∅ ∧
        BalancedRepairAdmissible ends m X k zero c Y ∧
        balancedSwap m X Y c = q) ↔
    fourColorMaskProfile m c = fourColorMaskProfile m q
  constructor
  · rintro ⟨X, Y, -, -, -, -, -, hswap⟩
    calc
      fourColorMaskProfile m c =
          fourColorMaskProfile m (balancedSwap m X Y c) :=
        (fourColorMaskProfile_balancedSwap m X Y c).symm
      _ = fourColorMaskProfile m q := congrArg _ hswap
  · intro hprofile
    have hrepair := left_right_sameMasks_admissible hc hq
      (congrArg Prod.fst hprofile) (congrArg Prod.snd hprofile)
    exact ⟨balancedMiddleDifference m c q,
      balancedOuterDifference m c q,
      hrepair.1, hrepair.2.1, hrepair.2.2.1, hrepair.2.2.2.1,
      hrepair.2.2.2.2.1, hrepair.2.2.2.2.2⟩


end StatMech.GrahamGHS.FourColor
