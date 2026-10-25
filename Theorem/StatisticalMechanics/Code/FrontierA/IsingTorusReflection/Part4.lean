/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusGaussianDomination.Part3
import Instance.StatisticalMechanics.Code.FrontierA.IsingTorusReflection
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}

theorem isingTorusStep_apply_same (i : Fin d) :
    isingTorusStep (k := k) i i = 1 := by
  simp [isingTorusStep]

theorem isingTorusStep_apply_of_ne (i j : Fin d) (hji : j ≠ i) :
    isingTorusStep (k := k) i j = 0 := by
  simp [isingTorusStep, hji]

theorem isingTorusReflectSite_add_step_same
    (i : Fin d) (x : IsingDyadicTorus d k) :
    isingTorusReflectSite i (x + isingTorusStep i) =
      isingTorusReflectSite i x - isingTorusStep i := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [isingTorusReflectSite_apply_same, isingTorusStep_apply_same,
      isingTorusReflectCoord_add_one]
  · simp [isingTorusReflectSite_apply_of_ne i j hji,
      isingTorusStep_apply_of_ne i j hji]

theorem isingTorusReflectSite_add_step_of_ne
    (i j : Fin d) (hji : j ≠ i) (x : IsingDyadicTorus d k) :
    isingTorusReflectSite i (x + isingTorusStep j) =
      isingTorusReflectSite i x + isingTorusStep j := by
  funext l
  by_cases hli : l = i
  · subst l
    have hij : i ≠ j := Ne.symm hji
    simp [isingTorusReflectSite_apply_same,
      isingTorusStep_apply_of_ne j i hij]
  · simp [isingTorusReflectSite_apply_of_ne i l hli]

theorem isingTorusReflectCoord_add_one_eq_of_lower_cross
    (z : ZMod (2 ^ (k + 2)))
    (hz : z.val < 2 ^ (k + 1))
    (hcross : ¬(z + 1).val < 2 ^ (k + 1)) :
    isingTorusReflectCoord (z + 1) = z := by
  apply ZMod.val_injective
  rw [isingTorusReflectCoord_val]
  have hzlt := z.val_lt
  have hside : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) :=
    isingTorus_side_eq_two_mul_half
  have hone : (1 : ZMod (2 ^ (k + 2))).val = 1 := by
    have hlt : 1 < 2 ^ (k + 2) := by
      rw [hside]
      have hp : 0 < 2 ^ (k + 1) := pow_pos (by omega) _
      omega
    letI : Fact (1 < 2 ^ (k + 2)) := ⟨hlt⟩
    exact ZMod.val_one (2 ^ (k + 2))
  have hsumlt : z.val + (1 : ZMod (2 ^ (k + 2))).val <
      2 ^ (k + 2) := by rw [hone]; omega
  rw [ZMod.val_add_of_lt hsumlt] at hcross ⊢
  rw [hone] at hcross ⊢
  omega

theorem isingTorusReflectCoord_eq_add_one_of_upper_cross
    (z : ZMod (2 ^ (k + 2)))
    (hz : ¬z.val < 2 ^ (k + 1))
    (hcross : (z + 1).val < 2 ^ (k + 1)) :
    isingTorusReflectCoord z = z + 1 := by
  apply ZMod.val_injective
  rw [isingTorusReflectCoord_val]
  have hzlt := z.val_lt
  have hside : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) :=
    isingTorus_side_eq_two_mul_half
  have hone : (1 : ZMod (2 ^ (k + 2))).val = 1 := by
    have hlt : 1 < 2 ^ (k + 2) := by
      rw [hside]
      have hp : 0 < 2 ^ (k + 1) := pow_pos (by omega) _
      omega
    letI : Fact (1 < 2 ^ (k + 2)) := ⟨hlt⟩
    exact ZMod.val_one (2 ^ (k + 2))
  by_cases hsumlt : z.val + (1 : ZMod (2 ^ (k + 2))).val <
      2 ^ (k + 2)
  · rw [ZMod.val_add_of_lt hsumlt] at hcross ⊢
    rw [hone] at hcross ⊢
    omega
  · have hle : 2 ^ (k + 2) ≤
        z.val + (1 : ZMod (2 ^ (k + 2))).val := by omega
    rw [ZMod.val_add_of_le hle]
    rw [hone] at hle ⊢
    omega

theorem isingTorus_crossing_reflects_endpoints
    (i j : Fin d) (x : IsingDyadicTorus d k) :
    (isingTorusInLowerHalf i x ∧
        ¬ isingTorusInLowerHalf i (x + isingTorusStep j) →
      isingTorusReflectSite i (x + isingTorusStep j) = x) ∧
    (¬ isingTorusInLowerHalf i x ∧
        isingTorusInLowerHalf i (x + isingTorusStep j) →
      isingTorusReflectSite i x = x + isingTorusStep j) := by
  constructor
  · rintro ⟨hx, hy⟩
    have hji : j = i := by
      by_contra hne
      apply hy
      unfold isingTorusInLowerHalf at hx ⊢
      rw [Pi.add_apply, isingTorusStep_apply_of_ne j i (Ne.symm hne)]
      simpa using hx
    subst j
    have hy' : ¬(x i + 1).val < 2 ^ (k + 1) := by
      unfold isingTorusInLowerHalf at hy
      simpa [Pi.add_apply, isingTorusStep_apply_same] using hy
    funext l
    by_cases hli : l = i
    · subst l
      rw [isingTorusReflectSite_apply_same, Pi.add_apply,
        isingTorusStep_apply_same]
      exact congrArg id
        (isingTorusReflectCoord_add_one_eq_of_lower_cross
          (x i) hx hy')
    · simp [isingTorusReflectSite_apply_of_ne i l hli,
        isingTorusStep_apply_of_ne i l hli]
  · rintro ⟨hx, hy⟩
    have hji : j = i := by
      by_contra hne
      apply hx
      unfold isingTorusInLowerHalf at hy ⊢
      rw [Pi.add_apply,
        isingTorusStep_apply_of_ne j i (Ne.symm hne)] at hy
      simpa using hy
    subst j
    have hy' : (x i + 1).val < 2 ^ (k + 1) := by
      unfold isingTorusInLowerHalf at hy
      simpa [Pi.add_apply, isingTorusStep_apply_same] using hy
    funext l
    by_cases hli : l = i
    · subst l
      rw [isingTorusReflectSite_apply_same, Pi.add_apply,
        isingTorusStep_apply_same]
      exact congrArg id
        (isingTorusReflectCoord_eq_add_one_of_upper_cross
          (x i) hx hy')
    · simp [isingTorusReflectSite_apply_of_ne i l hli,
        isingTorusStep_apply_of_ne i l hli]

@[simp] theorem isingTorusReflectSite_involutive
    (i : Fin d) (x : IsingDyadicTorus d k) :
    isingTorusReflectSite i (isingTorusReflectSite i x) = x := by
  funext j
  by_cases hji : j = i
  · subst j
    simp
  · simp [isingTorusReflectSite_apply_of_ne i j hji]

theorem isingTorusReflectSite_not_lower_iff
    (i : Fin d) (x : IsingDyadicTorus d k) :
    isingTorusInLowerHalf i (isingTorusReflectSite i x) ↔
      ¬ isingTorusInLowerHalf i x := by
  unfold isingTorusInLowerHalf
  rw [isingTorusReflectSite_apply_same, isingTorusReflectCoord_val]
  have hx := (x i).val_lt
  have hhpos : 0 < 2 ^ (k + 1) := pow_pos (by omega) _
  have hside : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) :=
    isingTorus_side_eq_two_mul_half
  omega


end StatMech.FrontierA
