/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorAdmissibleRepair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorInvariantMasks
import Def.StatisticalMechanics.Code.FrontierA.GrahamFourColorAdmissibleRepair.Part2
open Finset
open Classical
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {ι W : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype W] [DecidableEq W]


theorem balancedRepairRelated_symm
    (ends : ι -> Sym2 W) (m X : Finset ι) (k zero : W)
    {c d : ↑m -> Fin 4}
    (h : BalancedRepairRelated ends m X k zero c d) :
    BalancedRepairRelated ends m X k zero d c := by
  rcases h with ⟨Y, hY, rfl⟩
  refine ⟨Y, balancedRepairAdmissible_swap ends m X k zero c Y hY, ?_⟩
  exact (balancedSwap_involutive m X Y c).symm


end StatMech.GrahamGHS.FourColor
