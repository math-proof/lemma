/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamRowDataRepairRelation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamComponentExchangeWeightedCounterexample.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorUniformMaskSelector.Part4
open Finset


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


def RowDataRepairRelated
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (d : leftRowData ends m j k l zero)
    (e : rightRowData ends m j k l zero) : Prop :=
  let c := (rowDataToLeftFiber ends m j k l zero d).1
  let q := (rowDataToRightFiber ends m j k l zero e).1
  ∃ X Y : Finset I,
    X ⊆ middleMask m c ∧
      Y ⊆ outerMask m c ∧
      sources ends X = {k, l} ∧
      sources ends Y = ∅ ∧
      BalancedRepairAdmissible ends m X k zero c Y ∧
      balancedSwap m X Y c = q


noncomputable def admissibleRightRowRepairs
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (d : leftRowData ends m j k l zero) :
    Finset (rightRowData ends m j k l zero) := by
  classical
  exact Finset.univ.filter (RowDataRepairRelated ends m j k l zero d)

end StatMech.GrahamGHS.FourColor
