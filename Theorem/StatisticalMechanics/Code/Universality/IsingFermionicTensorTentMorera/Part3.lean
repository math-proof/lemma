/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDenseIncidencePrimitiveBridge.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectedTensorTent.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCenteredRadialPatch.Part12
import Def.StatisticalMechanics.Code.Universality.IsingFermionicTensorTentMorera


namespace StatMech.Universality

open Filter Set Topology

open scoped BigOperators

noncomputable section

theorem complexDisplacementIntegral_reverse
    (f : Complex -> Complex) (a v : Complex) :
    complexDisplacementIntegral f (a + v) (-v) =
      -complexDisplacementIntegral f a v := by
  unfold complexDisplacementIntegral
  have hpoint (t : Real) :
      f (a + v + (t : Complex) * -v) * -v =
        -(f (a + ((1 - t : Real) : Complex) * v) * v) := by
    have harg : a + v + (t : Complex) * -v =
        a + ((1 - t : Real) : Complex) * v := by
      push_cast
      ring
    rw [harg]
    ring
  simp_rw [hpoint]
  rw [intervalIntegral.integral_neg,
    intervalIntegral.integral_comp_sub_left
      (fun t : Real => f (a + (t : Complex) * v) * v) 1]
  norm_num


theorem complexDisplacementIntegral_ofReal
    (f : Complex -> Complex) (x y d : Real) :
    complexDisplacementIntegral f (x + y * Complex.I) d =
      ∫ s : Real in x..x + d, f (s + y * Complex.I) := by
  unfold complexDisplacementIntegral
  have hpoint (t : Real) :
      f ((x : Complex) + y * Complex.I + (t : Complex) * (d : Complex)) *
          (d : Complex) =
        (d : Complex) * f ((x + d * t : Real) + y * Complex.I) := by
    have harg : (x : Complex) + y * Complex.I +
        (t : Complex) * (d : Complex) =
      ((x + d * t : Real) : Complex) + y * Complex.I := by
      push_cast
      ring
    rw [harg]
    ring
  simp_rw [hpoint, ← smul_eq_mul]
  simpa [add_comm] using
    (intervalIntegral.smul_integral_comp_add_mul
      (f := fun s : Real => f (s + y * Complex.I))
      (a := (0 : Real)) (b := 1) d x)


theorem complexDisplacementIntegral_mul_I
    (f : Complex -> Complex) (x y d : Real) :
    complexDisplacementIntegral f (x + y * Complex.I)
        ((d : Complex) * Complex.I) =
      Complex.I * ∫ s : Real in y..y + d, f (x + s * Complex.I) := by
  unfold complexDisplacementIntegral
  have hpoint (t : Real) :
      f ((x : Complex) + y * Complex.I +
          (t : Complex) * ((d : Complex) * Complex.I)) *
          ((d : Complex) * Complex.I) =
        Complex.I * ((d : Complex) *
          f ((x : Complex) + (y + d * t : Real) * Complex.I)) := by
    have harg : (x : Complex) + y * Complex.I +
        (t : Complex) * ((d : Complex) * Complex.I) =
      (x : Complex) + (y + d * t : Real) * Complex.I := by
      push_cast
      ring
    rw [harg]
    ring
  simp_rw [hpoint, intervalIntegral.integral_const_mul]
  congr 1
  simpa [smul_eq_mul, add_comm] using
    (intervalIntegral.smul_integral_comp_add_mul
      (f := fun s : Real => f ((x : Complex) + s * Complex.I))
      (a := (0 : Real)) (b := 1) d y)


theorem axisRectangleDisplacementContour_eq_wedgeContour
    (f : Complex -> Complex) (x y width height : Real) :
    complexDisplacementIntegral f (x + y * Complex.I) width +
        complexDisplacementIntegral f
          ((x + width : Real) + y * Complex.I)
          ((height : Complex) * Complex.I) +
        complexDisplacementIntegral f
          ((x + width : Real) + (y + height : Real) * Complex.I)
          ((-width : Real) : Complex) +
        complexDisplacementIntegral f
          (x + (y + height : Real) * Complex.I)
          ((-height : Real) * Complex.I) =
      Complex.wedgeIntegral (x + y * Complex.I)
          ((x + width : Real) + (y + height : Real) * Complex.I) f +
        Complex.wedgeIntegral
          ((x + width : Real) + (y + height : Real) * Complex.I)
          (x + y * Complex.I) f := by
  rw [complexDisplacementIntegral_ofReal,
    complexDisplacementIntegral_mul_I,
    complexDisplacementIntegral_ofReal,
    complexDisplacementIntegral_mul_I]
  unfold Complex.wedgeIntegral
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero,
    sub_zero, add_zero, Complex.add_im, mul_one, zero_add, smul_eq_mul]
  simp only [mul_comm Complex.I]
  have hcomm :
      (∫ s : Real in x..x + width, f ((s : Complex) + y * Complex.I)) =
        ∫ s : Real in x..x + width, f (y * Complex.I + (s : Complex)) := by
    apply intervalIntegral.integral_congr
    intro s _hs
    exact congrArg f (add_comm (s : Complex) (y * Complex.I))
  rw [hcomm]
  ring


theorem sum_horizontalComplexDisplacementIntegral
    (f : Complex -> Complex) (hf : Continuous f)
    (x y mesh : Real) (N : Nat) :
    (∑ k ∈ Finset.range N,
      complexDisplacementIntegral f
        ((x + (k : Real) * mesh : Real) + y * Complex.I) mesh) =
      complexDisplacementIntegral f (x + y * Complex.I)
        ((((N : Real) * mesh) : Real) : Complex) := by
  let a : Nat -> Real := fun k => x + (k : Real) * mesh
  let g : Real -> Complex := fun s => f (s + y * Complex.I)
  have hg : Continuous g := hf.comp (by fun_prop)
  have hint : ∀ k < N,
      IntervalIntegrable g MeasureTheory.volume (a k) (a (k + 1)) :=
    fun k _hk => hg.intervalIntegrable _ _
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hint
  simp_rw [complexDisplacementIntegral_ofReal]
  simpa [a, g, Nat.cast_add, add_mul, add_assoc] using hsum


theorem sum_verticalComplexDisplacementIntegral
    (f : Complex -> Complex) (hf : Continuous f)
    (x y mesh : Real) (N : Nat) :
    (∑ k ∈ Finset.range N,
      complexDisplacementIntegral f
        (x + (y + (k : Real) * mesh : Real) * Complex.I)
        ((mesh : Complex) * Complex.I)) =
      complexDisplacementIntegral f (x + y * Complex.I)
        (((N : Real) * mesh : Real) * Complex.I) := by
  let a : Nat -> Real := fun k => y + (k : Real) * mesh
  let g : Real -> Complex := fun s => f (x + s * Complex.I)
  have hg : Continuous g := hf.comp (by fun_prop)
  have hint : ∀ k < N,
      IntervalIntegrable g MeasureTheory.volume (a k) (a (k + 1)) :=
    fun k _hk => hg.intervalIntegrable _ _
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hint
  simp_rw [complexDisplacementIntegral_mul_I]
  rw [← Finset.mul_sum]
  congr 1
  simpa [a, g, Nat.cast_add, add_mul, add_assoc] using hsum


end
end StatMech.Universality
