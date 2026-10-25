/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSpinReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusGraph.Part4
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Algebra.QuadraticDiscriminant
import Def.StatisticalMechanics.Code.FrontierA.IsingTorusSpinReflection.Part2
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}


theorem isingTorusUpperValues_zero
    (i : Fin d)
    (sigma : ConfigSpace (IsingTorusLowerSite (k := k) i)) :
    isingTorusUpperValues i 0 sigma =
      isingTorusLowerValues i 0 sigma := by
  funext x
  simp [isingTorusUpperValues, isingTorusLowerValues]


theorem isingTorusHalfReflectionForm_spin_eq
    (i : Fin d) (beta : Real)
    (x y : IsingTorusLowerSite (k := k) i) :
    isingTorusHalfReflectionForm i beta
        (isingTorusHalfSpin x) (isingTorusHalfSpin y) =
      ∑ sigma : ConfigSpace (IsingDyadicTorus d k),
        Real.exp (-(beta / 2) *
          isingTorusDirichlet (isingTorusSpinField sigma)) *
          isingTorusSpinField sigma x.1 *
          isingTorusSpinField sigma (isingTorusReflectSite i y.1) := by
  rw [← (isingTorusHalvesEquiv (k := k) i).bijective.sum_comp
    (fun sigma : ConfigSpace (IsingDyadicTorus d k) =>
      Real.exp (-(beta / 2) *
        isingTorusDirichlet (isingTorusSpinField sigma)) *
        isingTorusSpinField sigma x.1 *
        isingTorusSpinField sigma (isingTorusReflectSite i y.1)),
    Fintype.sum_prod_type]
  unfold isingTorusHalfReflectionForm
  apply Finset.sum_congr rfl
  intro lower _
  apply Finset.sum_congr rfl
  intro upper _
  have hequiv : (isingTorusHalvesEquiv (k := k) i) (lower, upper) =
      isingTorusGlueHalves i lower upper := rfl
  rw [hequiv]
  have hry : ¬ isingTorusInLowerHalf i
      (isingTorusReflectSite i y.1) :=
    fun h => (isingTorusReflectSite_not_lower_iff i y.1).mp h y.2
  have hfield :
      isingTorusSpinField (isingTorusGlueHalves i lower upper) =
        isingTorusEmbedLower i (isingTorusLowerValues i 0 lower) +
          isingTorusEmbedUpper i (isingTorusUpperValues i 0 upper) := by
    simpa using isingTorusSpinGlue_add_field_eq_embeds i 0 lower upper
  have hweight :
      Real.exp (-(beta / 2) * isingTorusDirichlet
          (isingTorusSpinField (isingTorusGlueHalves i lower upper))) =
        isingTorusLowerHalfWeight i beta
            (isingTorusLowerValues i 0 lower) *
          isingTorusLowerHalfWeight i beta
            (isingTorusLowerValues i 0 upper) *
          Real.exp (beta *
            ∑ e : IsingTorusDirectedEdge d k,
              isingTorusBoundaryFeature i
                  (isingTorusLowerValues i 0 lower) e *
                isingTorusBoundaryFeature i
                  (isingTorusLowerValues i 0 upper) e) := by
    rw [hfield, isingTorus_shiftedWeight_factor_boundary,
      isingTorusUpperHalfWeight_eq_lowerHalfWeight,
      isingTorusUpperValues_zero]
  have hgluex : isingTorusGlueHalves i lower upper x.1 = lower x := by
    simp [isingTorusGlueHalves, x.2]
  have hgluey : isingTorusGlueHalves i lower upper
      (isingTorusReflectSite i y.1) = upper y := by
    simp [isingTorusGlueHalves, hry]
  have hspinx : spin (isingTorusGlueHalves i lower upper) x.1 =
      spin lower x := by
    unfold spin
    rw [hgluex]
  have hspiny : spin (isingTorusGlueHalves i lower upper)
      (isingTorusReflectSite i y.1) = spin upper y := by
    unfold spin
    rw [hgluey]
  rw [hweight]
  simp only [isingTorusHalfSpin, isingTorusSpinField]
  rw [hspinx, hspiny]
  ring


theorem isingTorusTwoPoint_reflection_cauchy
    (i : Fin d) (beta : Real) (hbeta : 0 ≤ beta)
    (x y : IsingTorusLowerSite (k := k) i) :
    isingTorusTwoPoint beta x.1 (isingTorusReflectSite i y.1) ^ 2 ≤
      isingTorusTwoPoint beta x.1 (isingTorusReflectSite i x.1) *
        isingTorusTwoPoint beta y.1 (isingTorusReflectSite i y.1) := by
  have h := isingTorusHalfReflectionForm_cauchy i beta hbeta
    (isingTorusHalfSpin x) (isingTorusHalfSpin y)
  rw [isingTorusHalfReflectionForm_spin_eq,
    isingTorusHalfReflectionForm_spin_eq,
    isingTorusHalfReflectionForm_spin_eq] at h
  unfold isingTorusTwoPoint
  rw [div_pow, div_mul_div_comm]
  simpa only [pow_two] using div_le_div_of_nonneg_right h
    (sq_nonneg (isingTorusShiftedPartition (d := d) (k := k) beta 0))

theorem isingTorusTwoPoint_symm
    (beta : Real) (x y : IsingDyadicTorus d k) :
    isingTorusTwoPoint beta x y = isingTorusTwoPoint beta y x := by
  unfold isingTorusTwoPoint
  congr 1
  apply Finset.sum_congr rfl
  intro sigma _
  ring

theorem isingTorusTwoPoint_origin_neg
    (beta : Real) (z : IsingDyadicTorus d k) :
    isingTorusTwoPoint beta 0 (-z) =
      isingTorusTwoPoint beta 0 z := by
  calc
    isingTorusTwoPoint beta 0 (-z) =
        isingTorusTwoPoint beta z 0 := by
      simpa using isingTorusTwoPoint_translate (-z) z 0 beta
    _ = isingTorusTwoPoint beta 0 z :=
      isingTorusTwoPoint_symm beta z 0

theorem isingTorusCoordinateShift_add
    (i : Fin d) (a b : Nat) :
    isingTorusCoordinateShift (k := k) i (a + b) =
      isingTorusCoordinateShift i a + isingTorusCoordinateShift i b := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [isingTorusCoordinateShift]
  · simp [isingTorusCoordinateShift, hji]

theorem isingTorusCoordinateShift_one
    (i : Fin d) :
    isingTorusCoordinateShift (k := k) i 1 = isingTorusStep i := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [isingTorusCoordinateShift, isingTorusStep]
  · simp [isingTorusCoordinateShift, isingTorusStep, hji]

theorem isingTorusReflectSite_coordinateShift
    (i : Fin d) (n : Nat) :
    isingTorusReflectSite i (isingTorusCoordinateShift (k := k) i n) =
      -isingTorusCoordinateShift i n - isingTorusStep i := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [isingTorusReflectSite_apply_same,
      isingTorusCoordinateShift_apply_same,
      isingTorusStep_apply_same,
      isingTorusReflectCoord_eq_neg_sub_one]
  · simp [isingTorusReflectSite_apply_of_ne i j hji,
      isingTorusCoordinateShift_apply_of_ne i j hji,
      isingTorusStep_apply_of_ne i j hji]

theorem isingTorusCoordinateShift_sum_succ
    (i : Fin d) (a b : Nat) :
    isingTorusCoordinateShift (k := k) i (a + b + 1) =
      isingTorusCoordinateShift i a +
        isingTorusCoordinateShift i b + isingTorusStep i := by
  rw [isingTorusCoordinateShift_add i (a + b) 1,
    isingTorusCoordinateShift_add i a b,
    isingTorusCoordinateShift_one]


theorem isingTorusTwoPoint_axis_midpoint_sq_le
    (i : Fin d) (beta : Real) (hbeta : 0 ≤ beta)
    (a b : Nat) (ha : a < 2 ^ (k + 1)) (hb : b < 2 ^ (k + 1)) :
    isingTorusTwoPoint (k := k) beta 0
        (isingTorusCoordinateShift i (a + b + 1)) ^ 2 ≤
      isingTorusTwoPoint (k := k) beta 0
          (isingTorusCoordinateShift i (2 * a + 1)) *
        isingTorusTwoPoint (k := k) beta 0
          (isingTorusCoordinateShift i (2 * b + 1)) := by
  let x : IsingTorusLowerSite (k := k) i :=
    ⟨isingTorusCoordinateShift i a, by
      unfold isingTorusInLowerHalf
      rw [isingTorusCoordinateShift_apply_same,
        ZMod.val_natCast_of_lt]
      · exact ha
      · have hp : 0 < 2 ^ (k + 1) := pow_pos (by omega) _
        have hside : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by
          rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
          ring
        omega⟩
  let y : IsingTorusLowerSite (k := k) i :=
    ⟨isingTorusCoordinateShift i b, by
      unfold isingTorusInLowerHalf
      rw [isingTorusCoordinateShift_apply_same,
        ZMod.val_natCast_of_lt]
      · exact hb
      · have hp : 0 < 2 ^ (k + 1) := pow_pos (by omega) _
        have hside : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by
          rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
          ring
        omega⟩
  have h := isingTorusTwoPoint_reflection_cauchy i beta hbeta x y
  have hxy : isingTorusReflectSite i y.1 - x.1 =
      -isingTorusCoordinateShift i (a + b + 1) := by
    dsimp only [x, y]
    rw [isingTorusReflectSite_coordinateShift,
      isingTorusCoordinateShift_sum_succ]
    abel
  have hxx : isingTorusReflectSite i x.1 - x.1 =
      -isingTorusCoordinateShift i (2 * a + 1) := by
    dsimp only [x]
    rw [isingTorusReflectSite_coordinateShift]
    have hs := isingTorusCoordinateShift_sum_succ (k := k) i a a
    rw [show a + a + 1 = 2 * a + 1 by omega] at hs
    rw [hs]
    abel
  have hyy : isingTorusReflectSite i y.1 - y.1 =
      -isingTorusCoordinateShift i (2 * b + 1) := by
    dsimp only [y]
    rw [isingTorusReflectSite_coordinateShift]
    have hs := isingTorusCoordinateShift_sum_succ (k := k) i b b
    rw [show b + b + 1 = 2 * b + 1 by omega] at hs
    rw [hs]
    abel
  have hcxy : isingTorusTwoPoint beta x.1
      (isingTorusReflectSite i y.1) =
        isingTorusTwoPoint (k := k) beta 0
          (isingTorusCoordinateShift i (a + b + 1)) := by
    rw [isingTorusTwoPoint_eq_origin_displacement, hxy,
      isingTorusTwoPoint_origin_neg]
  have hcxx : isingTorusTwoPoint beta x.1
      (isingTorusReflectSite i x.1) =
        isingTorusTwoPoint (k := k) beta 0
          (isingTorusCoordinateShift i (2 * a + 1)) := by
    rw [isingTorusTwoPoint_eq_origin_displacement, hxx,
      isingTorusTwoPoint_origin_neg]
  have hcyy : isingTorusTwoPoint beta y.1
      (isingTorusReflectSite i y.1) =
        isingTorusTwoPoint (k := k) beta 0
          (isingTorusCoordinateShift i (2 * b + 1)) := by
    rw [isingTorusTwoPoint_eq_origin_displacement, hyy,
      isingTorusTwoPoint_origin_neg]
  calc
    isingTorusTwoPoint beta 0
          (isingTorusCoordinateShift i (a + b + 1)) ^ 2 =
        isingTorusTwoPoint beta x.1
          (isingTorusReflectSite i y.1) ^ 2 := by rw [hcxy]
    _ ≤ isingTorusTwoPoint beta x.1
          (isingTorusReflectSite i x.1) *
        isingTorusTwoPoint beta y.1
          (isingTorusReflectSite i y.1) := h
    _ = isingTorusTwoPoint beta 0
          (isingTorusCoordinateShift i (2 * a + 1)) *
        isingTorusTwoPoint beta 0
          (isingTorusCoordinateShift i (2 * b + 1)) := by
      rw [hcxx, hcyy]

end StatMech.FrontierA
