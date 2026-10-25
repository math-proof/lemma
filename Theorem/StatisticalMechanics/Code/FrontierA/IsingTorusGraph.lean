/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusStationarity
import Theorem.StatisticalMechanics.Code.Sharpness.HighTempSimon.Part8
import Theorem.StatisticalMechanics.Code.Sharpness.HighTempPlusBox.Part5
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Sharpness

variable {d k : Nat}

theorem isingDyadicSide_gt_two : 2 < 2 ^ (k + 2) := by
  have : 2 ^ 2 ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by omega) (by omega)
  norm_num at this ⊢
  omega

theorem isingTorus_zmod_one_ne_zero :
    (1 : ZMod (2 ^ (k + 2))) ≠ 0 := by
  rw [Ne, ← Nat.cast_one, ZMod.natCast_eq_zero_iff]
  intro hdvd
  have := Nat.le_of_dvd (by norm_num : 0 < 1) hdvd
  have hside := isingDyadicSide_gt_two (k := k)
  omega

theorem isingTorus_zmod_two_ne_zero :
    (2 : ZMod (2 ^ (k + 2))) ≠ 0 := by
  have h : ((2 : Nat) : ZMod (2 ^ (k + 2))) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have := Nat.le_of_dvd (by norm_num : 0 < 2) hdvd
    have hside := isingDyadicSide_gt_two (k := k)
    omega
  simpa using h

theorem isingTorusStep_ne_zero (i : Fin d) :
    (isingTorusStep i : IsingDyadicTorus d k) ≠ 0 := by
  intro h
  have hi := congrFun h i
  simp [isingTorusStep, isingTorus_zmod_one_ne_zero] at hi


end StatMech.FrontierA
