/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusGaussianDomination.Part3
import Def.StatisticalMechanics.Code.FrontierA.IsingTorusReflection
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}

@[simp] theorem isingTorusReflectCoord_val
    (z : ZMod (2 ^ (k + 2))) :
    (isingTorusReflectCoord z).val = 2 ^ (k + 2) - 1 - z.val := by
  unfold isingTorusReflectCoord
  rw [ZMod.val_natCast]
  apply Nat.mod_eq_of_lt
  have hz := z.val_lt
  have hpos : 0 < 2 ^ (k + 2) := pow_pos (by omega) _
  omega

@[simp] theorem isingTorusReflectCoord_involutive
    (z : ZMod (2 ^ (k + 2))) :
    isingTorusReflectCoord (isingTorusReflectCoord z) = z := by
  apply ZMod.val_injective
  rw [isingTorusReflectCoord_val, isingTorusReflectCoord_val]
  have hz := z.val_lt
  have hpos : 0 < 2 ^ (k + 2) := pow_pos (by omega) _
  omega

theorem isingTorusReflectCoord_eq_neg_sub_one
    (z : ZMod (2 ^ (k + 2))) :
    isingTorusReflectCoord z = -z - 1 := by
  have hpos : 0 < 2 ^ (k + 2) := pow_pos (by omega) _
  have hz := z.val_lt
  have hnat : 2 ^ (k + 2) - 1 - z.val + z.val + 1 =
      2 ^ (k + 2) := by omega
  have hsum : isingTorusReflectCoord z + z + 1 = 0 := by
    rw [show isingTorusReflectCoord z + z + 1 =
      ((2 ^ (k + 2) - 1 - z.val : Nat) : ZMod (2 ^ (k + 2))) +
        (z.val : ZMod (2 ^ (k + 2))) + 1 by
      rw [ZMod.natCast_zmod_val]
      rfl]
    rw [← Nat.cast_add]
    have hone : (1 : ZMod (2 ^ (k + 2))) =
        ((1 : Nat) : ZMod (2 ^ (k + 2))) := by norm_num
    rw [hone, ← Nat.cast_add, hnat, ZMod.natCast_self]
  calc
    isingTorusReflectCoord z =
        (isingTorusReflectCoord z + z + 1) - z - 1 := by ring
    _ = 0 - z - 1 := by rw [hsum]
    _ = -z - 1 := by ring

theorem isingTorusReflectCoord_add_one
    (z : ZMod (2 ^ (k + 2))) :
    isingTorusReflectCoord (z + 1) = isingTorusReflectCoord z - 1 := by
  rw [isingTorusReflectCoord_eq_neg_sub_one,
    isingTorusReflectCoord_eq_neg_sub_one]
  ring

theorem isingTorusReflectCoord_sub_one
    (z : ZMod (2 ^ (k + 2))) :
    isingTorusReflectCoord (z - 1) = isingTorusReflectCoord z + 1 := by
  rw [isingTorusReflectCoord_eq_neg_sub_one,
    isingTorusReflectCoord_eq_neg_sub_one]
  ring


end StatMech.FrontierA
