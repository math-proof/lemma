/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusDissemination.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusReflection.Part10
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusCharacter.Part3
import Def.StatisticalMechanics.Code.FrontierA.IsingTorusDissemination.Part5
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}


theorem isingTorus_blockShift_sub_val
    (s : Nat) (hs : s ≤ 2 ^ (k + 1))
    (z : ZMod (2 ^ (k + 2))) (hz : z.val < 2 * s) :
    (z - (2 ^ (k + 1) + s : Nat)).val =
      2 ^ (k + 1) - s + z.val := by
  have hside : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) :=
    isingTorus_side_eq_two_mul_half'
  have hpos : 0 < 2 ^ (k + 1) := pow_pos (by omega) _
  by_cases heq : s = 2 ^ (k + 1)
  · subst s
    have hcast :
        ((2 ^ (k + 1) + 2 ^ (k + 1) : Nat) :
          ZMod (2 ^ (k + 2))) = 0 := by
      rw [← two_mul, ← hside]
      exact ZMod.natCast_self _
    rw [hcast, sub_zero]
    omega
  · have hslt : s < 2 ^ (k + 1) := by omega
    have hnlt : 2 ^ (k + 1) - s + z.val < 2 ^ (k + 2) := by
      omega
    have hnat : z.val + 2 ^ (k + 2) =
        (2 ^ (k + 1) + s) + (2 ^ (k + 1) - s + z.val) := by
      omega
    have hnatcast := congrArg
      (fun n : Nat => (n : ZMod (2 ^ (k + 2)))) hnat
    simp only [Nat.cast_add, ZMod.natCast_self, add_zero] at hnatcast
    have heqmod : z - (2 ^ (k + 1) + s : Nat) =
        ((2 ^ (k + 1) - s + z.val : Nat) :
          ZMod (2 ^ (k + 2))) := by
      rw [← ZMod.natCast_zmod_val z]
      push_cast
      apply sub_eq_iff_eq_add.mpr
      simpa [Nat.cast_add, add_comm, add_left_comm, add_assoc] using hnatcast
    rw [heqmod, ZMod.val_natCast_of_lt hnlt]

theorem isingTorus_blockShift_lower_of_lt
    (i : Fin d) (s : Nat) (hs : s ≤ 2 ^ (k + 1))
    (x : IsingDyadicTorus d k) (hx : (x i).val < s) :
    isingTorusInLowerHalf i (x - isingTorusBlockShift i s) := by
  unfold isingTorusInLowerHalf isingTorusBlockShift
  rw [Pi.sub_apply, isingTorusCoordinateShift_apply_same]
  rw [isingTorus_blockShift_sub_val s hs (x i) (by omega)]
  omega

theorem isingTorus_blockShift_not_lower_of_mem_second
    (i : Fin d) (s : Nat) (hspos : 0 < s)
    (hs : s ≤ 2 ^ (k + 1))
    (x : IsingDyadicTorus d k)
    (hxs : s ≤ (x i).val) (hx2s : (x i).val < 2 * s) :
    ¬ isingTorusInLowerHalf i (x - isingTorusBlockShift i s) := by
  unfold isingTorusInLowerHalf isingTorusBlockShift
  rw [Pi.sub_apply, isingTorusCoordinateShift_apply_same]
  rw [isingTorus_blockShift_sub_val s hs (x i) hx2s]
  omega

theorem isingTorus_block_reflected_site
    (i : Fin d) (s : Nat) (hspos : 0 < s)
    (hs : s ≤ 2 ^ (k + 1))
    (x : IsingDyadicTorus d k)
    (hxs : s ≤ (x i).val) (hx2s : (x i).val < 2 * s) :
    isingTorusReflectSite i (x - isingTorusBlockShift i s) +
        isingTorusBlockShift i s =
      Function.update x i
        ((2 * s - 1 - (x i).val : Nat) : ZMod (2 ^ (k + 2))) := by
  funext j
  by_cases hji : j = i
  · subst j
    rw [Pi.add_apply, isingTorusReflectSite_apply_same,
      isingTorusBlockShift, isingTorusCoordinateShift_apply_same,
      Pi.sub_apply, isingTorusCoordinateShift_apply_same]
    have hu : Function.update x i
        ((2 * s - 1 - (x i).val : Nat) : ZMod (2 ^ (k + 2))) i =
      ((2 * s - 1 - (x i).val : Nat) : ZMod (2 ^ (k + 2))) := by
      simp
    rw [hu]
    rw [isingTorusReflectCoord_eq_neg_sub_one]
    have hnat : 2 * s - 1 - (x i).val + (x i).val + 1 = 2 * s := by
      omega
    have hnatcast := congrArg
      (fun n : Nat => (n : ZMod (2 ^ (k + 2)))) hnat
    push_cast at hnatcast
    have hxcast : ((x i).val : ZMod (2 ^ (k + 2))) = x i :=
      ZMod.natCast_zmod_val (x i)
    have hrhs :
        ((2 * s - 1 - (x i).val : Nat) : ZMod (2 ^ (k + 2))) =
          2 * (s : ZMod (2 ^ (k + 2))) - 1 - x i := by
      calc
        ((2 * s - 1 - (x i).val : Nat) : ZMod (2 ^ (k + 2))) =
            2 * (s : ZMod (2 ^ (k + 2))) - 1 -
              ((x i).val : ZMod (2 ^ (k + 2))) := by
                linear_combination hnatcast
        _ = 2 * (s : ZMod (2 ^ (k + 2))) - 1 - x i := by
          rw [hxcast]
    rw [hrhs]
    have hside : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) :=
      isingTorus_side_eq_two_mul_half'
    have hhalf :
        (2 : ZMod (2 ^ (k + 2))) * (2 ^ (k + 1) : Nat) = 0 := by
      calc
        (2 : ZMod (2 ^ (k + 2))) * (2 ^ (k + 1) : Nat) =
            ((2 * 2 ^ (k + 1) : Nat) : ZMod (2 ^ (k + 2))) := by
              push_cast
              rfl
        _ = ((2 ^ (k + 2) : Nat) : ZMod (2 ^ (k + 2))) := by
          rw [hside]
        _ = 0 := ZMod.natCast_self _
    rw [Nat.cast_add]
    linear_combination hhalf
  · rw [Pi.add_apply, isingTorusReflectSite_apply_of_ne i j hji]
    simp [hji, isingTorusBlockShift,
      isingTorusCoordinateShift_apply_of_ne i j hji]

theorem isingTorus_block_reflected_val_lt
    (s : Nat) (hspos : 0 < s)
    (xval : Nat) (hxs : s ≤ xval) (hx2s : xval < 2 * s) :
    (2 * s - 1 - xval : Nat) < s := by
  omega

theorem isingTorusPolarizeLowerAt_eq_of_block_lt
    (i : Fin d) (s : Nat) (hs : s ≤ 2 ^ (k + 1))
    (h : IsingDyadicTorus d k → Real)
    (x : IsingDyadicTorus d k) (hx : (x i).val < s) :
    isingTorusPolarizeLowerAt i (isingTorusBlockShift i s) h x = h x := by
  unfold isingTorusPolarizeLowerAt isingTorusTranslateField
  rw [show x + -isingTorusBlockShift i s =
    x - isingTorusBlockShift i s by abel]
  simp only [isingTorusPolarizeLower,
    isingTorus_blockShift_lower_of_lt i s hs x hx, if_true]
  congr 1
  abel

theorem isingTorusPolarizeLowerAt_eq_of_mem_second
    (i : Fin d) (s : Nat) (hspos : 0 < s)
    (hs : s ≤ 2 ^ (k + 1))
    (h : IsingDyadicTorus d k → Real)
    (x : IsingDyadicTorus d k)
    (hxs : s ≤ (x i).val) (hx2s : (x i).val < 2 * s) :
    isingTorusPolarizeLowerAt i (isingTorusBlockShift i s) h x =
      h (Function.update x i
        ((2 * s - 1 - (x i).val : Nat) : ZMod (2 ^ (k + 2)))) := by
  unfold isingTorusPolarizeLowerAt isingTorusTranslateField
  rw [show x + -isingTorusBlockShift i s =
    x - isingTorusBlockShift i s by abel]
  simp only [isingTorusPolarizeLower,
    isingTorus_blockShift_not_lower_of_mem_second i s hspos hs x hxs hx2s,
    if_false]
  rw [isingTorus_block_reflected_site i s hspos hs x hxs hx2s]


theorem isingTorusDisseminatedBlock_double
    (i : Fin d) (s : Nat) (hspos : 0 < s)
    (hs : s ≤ 2 ^ (k + 1))
    (h : IsingDyadicTorus d k → Real)
    (hblock : IsingTorusDisseminatedBlock i s h) :
    IsingTorusDisseminatedBlock i (2 * s)
      (isingTorusPolarizeLowerAt i (isingTorusBlockShift i s) h) := by
  intro x hx
  have hzeroVal : ((Function.update x i 0) i).val < s := by
    simp
    exact hspos
  rw [isingTorusPolarizeLowerAt_eq_of_block_lt i s hs h
    (Function.update x i 0) hzeroVal]
  by_cases hxs : (x i).val < s
  · rw [isingTorusPolarizeLowerAt_eq_of_block_lt i s hs h x hxs]
    exact hblock x hxs
  · have hxs' : s ≤ (x i).val := by omega
    let y := Function.update x i
      ((2 * s - 1 - (x i).val : Nat) : ZMod (2 ^ (k + 2)))
    have hyval : (y i).val = 2 * s - 1 - (x i).val := by
      have hylt := isingTorus_block_reflected_val_lt
        s hspos (x i).val hxs' hx
      have hside : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) :=
        isingTorus_side_eq_two_mul_half'
      have hlt : 2 * s - 1 - (x i).val < 2 ^ (k + 2) := by
        omega
      simp [y, ZMod.val_natCast_of_lt hlt]
    have hylt : (y i).val < s := by
      rw [hyval]
      exact isingTorus_block_reflected_val_lt s hspos _ hxs' hx
    rw [isingTorusPolarizeLowerAt_eq_of_mem_second
      i s hspos hs h x hxs' hx]
    simpa [y] using hblock y hylt


end StatMech.FrontierA
