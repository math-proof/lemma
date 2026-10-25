/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSiteReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusSpinReflection.Part2
import Def.StatisticalMechanics.Code.FrontierA.IsingTorusSiteReflection.Part9
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}

theorem isingTorusSiteReflectionForm_spin_eq
    (i : Fin d) (beta : Real)
    (x y : IsingTorusStrictLower (k := k) i) :
    isingTorusSiteReflectionForm i beta
        (isingTorusStrictHalfSpin x) (isingTorusStrictHalfSpin y) =
      ∑ sigma : ConfigSpace (IsingDyadicTorus d k),
        Real.exp (-(beta / 2) *
          isingTorusDirichlet (isingTorusSpinField sigma)) *
          isingTorusSpinField sigma x.1 *
          isingTorusSpinField sigma (isingTorusSiteReflect i y.1) := by
  rw [← (isingTorusSiteSplitEquiv (k := k) i).bijective.sum_comp
    (fun sigma : ConfigSpace (IsingDyadicTorus d k) =>
      Real.exp (-(beta / 2) *
        isingTorusDirichlet (isingTorusSpinField sigma)) *
        isingTorusSpinField sigma x.1 *
        isingTorusSpinField sigma (isingTorusSiteReflect i y.1))]
  simp only [Fintype.sum_prod_type]
  unfold isingTorusSiteReflectionForm
  apply Finset.sum_congr rfl
  intro boundary _
  apply Finset.sum_congr rfl
  intro lower _
  apply Finset.sum_congr rfl
  intro upper _
  have hequiv : (isingTorusSiteSplitEquiv (k := k) i)
      (boundary, (lower, upper)) =
        isingTorusSiteGlue i boundary lower upper := rfl
  rw [hequiv, isingTorusSiteWeight_factor]
  have hnp : ¬ isingTorusOnSitePlane i x.1 := by
    intro hp
    unfold isingTorusOnSitePlane at hp
    have hx := x.2
    unfold isingTorusInStrictLower at hx
    rcases hp with hp | hp <;> omega
  have hnpY : ¬ isingTorusOnSitePlane i y.1 := by
    intro hp
    unfold isingTorusOnSitePlane at hp
    have hy := y.2
    unfold isingTorusInStrictLower at hy
    rcases hp with hp | hp <;> omega
  have hnpRY := isingTorusSiteReflect_not_plane i hnpY
  have hnotRY : ¬ isingTorusInStrictLower i
      (isingTorusSiteReflect i y.1) := by
    rw [isingTorusSiteReflect_strictLower_iff_upper]
    exact not_lt_of_ge y.2.2.le
  have hgluex : isingTorusSiteGlue i boundary lower upper x.1 =
      lower x := by
    simp [isingTorusSiteGlue, hnp, x.2]
  have hgluey : isingTorusSiteGlue i boundary lower upper
      (isingTorusSiteReflect i y.1) = upper y := by
    simp [isingTorusSiteGlue, hnpRY, hnotRY]
  have hspinx : spin (isingTorusSiteGlue i boundary lower upper) x.1 =
      spin lower x := by
    unfold spin
    rw [hgluex]
  have hspiny : spin (isingTorusSiteGlue i boundary lower upper)
      (isingTorusSiteReflect i y.1) = spin upper y := by
    unfold spin
    rw [hgluey]
  simp only [isingTorusSpinField, isingTorusStrictHalfSpin]
  rw [hspinx, hspiny]
  ring

theorem isingTorusTwoPoint_siteReflection_cauchy
    (i : Fin d) (beta : Real)
    (x y : IsingTorusStrictLower (k := k) i) :
    isingTorusTwoPoint beta x.1 (isingTorusSiteReflect i y.1) ^ 2 ≤
      isingTorusTwoPoint beta x.1 (isingTorusSiteReflect i x.1) *
        isingTorusTwoPoint beta y.1 (isingTorusSiteReflect i y.1) := by
  have h := isingTorusSiteReflectionForm_cauchy i beta
    (isingTorusStrictHalfSpin x) (isingTorusStrictHalfSpin y)
  rw [isingTorusSiteReflectionForm_spin_eq,
    isingTorusSiteReflectionForm_spin_eq,
    isingTorusSiteReflectionForm_spin_eq] at h
  unfold isingTorusTwoPoint
  rw [div_pow, div_mul_div_comm]
  simpa only [pow_two] using div_le_div_of_nonneg_right h
    (sq_nonneg (isingTorusShiftedPartition (d := d) (k := k) beta 0))

theorem isingTorusSiteReflect_coordinateShift
    (i : Fin d) (n : Nat) :
    isingTorusSiteReflect i (isingTorusCoordinateShift (k := k) i n) =
      -isingTorusCoordinateShift i n := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [isingTorusSiteReflect_apply_same,
      isingTorusCoordinateShift_apply_same]
  · simp [isingTorusSiteReflect_apply_of_ne i j hji,
      isingTorusCoordinateShift_apply_of_ne i j hji]


theorem isingTorusTwoPoint_axis_site_midpoint_sq_le
    (i : Fin d) (beta : Real)
    (a b : Nat) (ha0 : 0 < a) (hb0 : 0 < b)
    (ha : a < 2 ^ (k + 1)) (hb : b < 2 ^ (k + 1)) :
    isingTorusTwoPoint (k := k) beta 0
        (isingTorusCoordinateShift i (a + b)) ^ 2 ≤
      isingTorusTwoPoint (k := k) beta 0
          (isingTorusCoordinateShift i (2 * a)) *
        isingTorusTwoPoint (k := k) beta 0
          (isingTorusCoordinateShift i (2 * b)) := by
  let x : IsingTorusStrictLower (k := k) i :=
    ⟨isingTorusCoordinateShift i a, by
      unfold isingTorusInStrictLower
      rw [isingTorusCoordinateShift_apply_same,
        ZMod.val_natCast_of_lt]
      · exact ⟨ha0, ha⟩
      · have hp : 0 < 2 ^ (k + 1) := pow_pos (by omega) _
        have hside := isingTorus_side_eq_two_half (k := k)
        omega⟩
  let y : IsingTorusStrictLower (k := k) i :=
    ⟨isingTorusCoordinateShift i b, by
      unfold isingTorusInStrictLower
      rw [isingTorusCoordinateShift_apply_same,
        ZMod.val_natCast_of_lt]
      · exact ⟨hb0, hb⟩
      · have hp : 0 < 2 ^ (k + 1) := pow_pos (by omega) _
        have hside := isingTorus_side_eq_two_half (k := k)
        omega⟩
  have h := isingTorusTwoPoint_siteReflection_cauchy i beta x y
  have hxy : isingTorusSiteReflect i y.1 - x.1 =
      -isingTorusCoordinateShift i (a + b) := by
    dsimp only [x, y]
    rw [isingTorusSiteReflect_coordinateShift,
      isingTorusCoordinateShift_add]
    abel
  have hxx : isingTorusSiteReflect i x.1 - x.1 =
      -isingTorusCoordinateShift i (2 * a) := by
    dsimp only [x]
    rw [isingTorusSiteReflect_coordinateShift]
    have hs := isingTorusCoordinateShift_add (k := k) i a a
    rw [show a + a = 2 * a by omega] at hs
    rw [hs]
    abel
  have hyy : isingTorusSiteReflect i y.1 - y.1 =
      -isingTorusCoordinateShift i (2 * b) := by
    dsimp only [y]
    rw [isingTorusSiteReflect_coordinateShift]
    have hs := isingTorusCoordinateShift_add (k := k) i b b
    rw [show b + b = 2 * b by omega] at hs
    rw [hs]
    abel
  have hcxy : isingTorusTwoPoint beta x.1
      (isingTorusSiteReflect i y.1) =
        isingTorusTwoPoint (k := k) beta 0
          (isingTorusCoordinateShift i (a + b)) := by
    rw [isingTorusTwoPoint_eq_origin_displacement, hxy,
      isingTorusTwoPoint_origin_neg]
  have hcxx : isingTorusTwoPoint beta x.1
      (isingTorusSiteReflect i x.1) =
        isingTorusTwoPoint (k := k) beta 0
          (isingTorusCoordinateShift i (2 * a)) := by
    rw [isingTorusTwoPoint_eq_origin_displacement, hxx,
      isingTorusTwoPoint_origin_neg]
  have hcyy : isingTorusTwoPoint beta y.1
      (isingTorusSiteReflect i y.1) =
        isingTorusTwoPoint (k := k) beta 0
          (isingTorusCoordinateShift i (2 * b)) := by
    rw [isingTorusTwoPoint_eq_origin_displacement, hyy,
      isingTorusTwoPoint_origin_neg]
  calc
    isingTorusTwoPoint beta 0
          (isingTorusCoordinateShift i (a + b)) ^ 2 =
        isingTorusTwoPoint beta x.1
          (isingTorusSiteReflect i y.1) ^ 2 := by rw [hcxy]
    _ ≤ isingTorusTwoPoint beta x.1
          (isingTorusSiteReflect i x.1) *
        isingTorusTwoPoint beta y.1
          (isingTorusSiteReflect i y.1) := h
    _ = isingTorusTwoPoint beta 0
          (isingTorusCoordinateShift i (2 * a)) *
        isingTorusTwoPoint beta 0
          (isingTorusCoordinateShift i (2 * b)) := by
      rw [hcxx, hcyy]

end StatMech.FrontierA
