/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorAdmissibleRepair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorInvariantMasks
import Def.StatisticalMechanics.Code.FrontierA.GrahamFourColorAdmissibleRepair
open Finset
open Classical
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {ι W : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype W] [DecidableEq W]


@[simp] theorem mem_balancedRepairs_iff
    (ends : ι -> Sym2 W) (m X : Finset ι) (k zero : W)
    (c : ↑m -> Fin 4) (Y : Finset ι) :
    Y ∈ balancedRepairs ends m X k zero c ↔
      BalancedRepairAdmissible ends m X k zero c Y := by
  simp [balancedRepairs, BalancedRepairAdmissible]


theorem balancedRepairAdmissible_swap
    (ends : ι -> Sym2 W) (m X : Finset ι) (k zero : W)
    (c : ↑m -> Fin 4) (Y : Finset ι)
    (hY : BalancedRepairAdmissible ends m X k zero c Y) :
    BalancedRepairAdmissible ends m X k zero
      (balancedSwap m X Y c) Y := by
  refine ⟨?_, hY.2.1, hY.2.2.2, ?_⟩
  · rw [outerMask_balancedSwap]
    exact hY.1
  · rw [balancedSwap_involutive]
    exact hY.2.2.1


theorem balancedRepairAdmissible_swap_iff
    (ends : ι -> Sym2 W) (m X : Finset ι) (k zero : W)
    (c : ↑m -> Fin 4) (Y : Finset ι) :
    BalancedRepairAdmissible ends m X k zero
        (balancedSwap m X Y c) Y ↔
      BalancedRepairAdmissible ends m X k zero c Y := by
  constructor
  · intro h
    have hs := balancedRepairAdmissible_swap ends m X k zero
      (balancedSwap m X Y c) Y h
    simpa only [balancedSwap_involutive] using hs
  · exact balancedRepairAdmissible_swap ends m X k zero c Y


theorem mem_balancedRepairs_swap_iff
    (ends : ι -> Sym2 W) (m X : Finset ι) (k zero : W)
    (c : ↑m -> Fin 4) (Y : Finset ι) :
    Y ∈ balancedRepairs ends m X k zero (balancedSwap m X Y c) ↔
      Y ∈ balancedRepairs ends m X k zero c := by
  simp only [mem_balancedRepairs_iff, balancedRepairAdmissible_swap_iff]


end StatMech.GrahamGHS.FourColor
