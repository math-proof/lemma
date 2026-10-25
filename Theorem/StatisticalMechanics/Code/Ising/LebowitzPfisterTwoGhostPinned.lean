/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterTwoGhostPinned.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterGhostLift.Part2
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterTwoGhostPinned
open Finset
open scoped BigOperators


namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {W V : Type*} [Fintype W] [DecidableEq W]
  [Fintype V] [DecidableEq V]


@[simp] theorem lpTwoGhostPinnedConfig_inl
    (tau : ConfigSpace W) (x : W) :
    lpTwoGhostPinnedConfig tau (.inl x) = tau x := rfl

@[simp] theorem lpTwoGhostPinnedConfig_inr
    (tau : ConfigSpace W) (b : Bool) :
    lpTwoGhostPinnedConfig tau (.inr b) = !b := rfl

@[simp] theorem spin_lpTwoGhostPinnedConfig_inl
    (tau : ConfigSpace W) (x : W) :
    spin (lpTwoGhostPinnedConfig tau) (.inl x) = spin tau x := rfl

@[simp] theorem spin_lpTwoGhostPinnedConfig_inr_false
    (tau : ConfigSpace W) :
    spin (lpTwoGhostPinnedConfig tau) (.inr false) = 1 := by
  simp [spin, lpTwoGhostPinnedConfig]

@[simp] theorem spin_lpTwoGhostPinnedConfig_inr_true
    (tau : ConfigSpace W) :
    spin (lpTwoGhostPinnedConfig tau) (.inr true) = -1 := by
  simp [spin, lpTwoGhostPinnedConfig]


end
end StatMech.Ising
