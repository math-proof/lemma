/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorAdmissibleRepair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorInvariantMasks
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorAdmissibleRepair
open Finset
open Classical
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {ι W : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype W] [DecidableEq W]


def BalancedRepairRelated (ends : ι -> Sym2 W) (m X : Finset ι)
    (k zero : W) (c d : ↑m -> Fin 4) : Prop :=
  ∃ Y, BalancedRepairAdmissible ends m X k zero c Y ∧
    d = balancedSwap m X Y c


end StatMech.GrahamGHS.FourColor
