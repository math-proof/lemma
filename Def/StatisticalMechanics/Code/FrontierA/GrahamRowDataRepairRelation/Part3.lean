/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamRowDataRepairRelation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamComponentExchangeWeightedCounterexample.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorUniformMaskSelector.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamRowDataRepairRelation.Part2
open Finset


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


noncomputable def admissibleRightRowNeighborhood
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (S : Finset (leftRowData ends m j k l zero)) :
    Finset (rightRowData ends m j k l zero) := by
  classical
  exact Finset.univ.filter fun e =>
    ∃ d ∈ S, RowDataRepairRelated ends m j k l zero d e

end StatMech.GrahamGHS.FourColor
