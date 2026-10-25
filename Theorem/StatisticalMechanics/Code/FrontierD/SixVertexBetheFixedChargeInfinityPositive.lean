/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeInfinityPositive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeInfinityNonzero
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

theorem sum_Ioi_pair_add {n : Nat} (e : Fin n -> Real) :
    (∑ i, ∑ j ∈ Finset.Ioi i, (e i + e j)) =
      (n - 1 : Nat) * ∑ i, e i := by
  classical
  have hfirst :
      (∑ i, ∑ _j ∈ Finset.Ioi i, e i) =
        ∑ i, (n - 1 - i.val : Nat) * e i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_const, nsmul_eq_mul, Fin.card_Ioi]
  have hsecond :
      (∑ i, ∑ j ∈ Finset.Ioi i, e j) =
        ∑ j, j.val * e j := by
    calc
      (∑ i, ∑ j ∈ Finset.Ioi i, e j) =
          ∑ i, ∑ j, if i < j then e j else 0 := by
            apply Finset.sum_congr rfl
            intro i _
            have hIoi : Finset.Ioi i = Finset.univ.filter (fun j => i < j) := by
              ext j
              simp
            rw [hIoi]
            rw [← Finset.sum_filter]
      _ = ∑ j, ∑ i, if i < j then e j else 0 := Finset.sum_comm
      _ = ∑ j, j.val * e j := by
        apply Finset.sum_congr rfl
        intro j _
        have hIio : Finset.Iio j = Finset.univ.filter (fun i => i < j) := by
          ext i
          simp
        rw [← Finset.sum_filter, ← hIio]
        rw [Finset.sum_const, nsmul_eq_mul, Fin.card_Iio]
  calc
    (∑ i, ∑ j ∈ Finset.Ioi i, (e i + e j)) =
        (∑ i, ∑ _j ∈ Finset.Ioi i, e i) +
          ∑ i, ∑ j ∈ Finset.Ioi i, e j := by
            simp_rw [Finset.sum_add_distrib]
    _ = ∑ i, ((n - 1 - i.val : Nat) * e i + i.val * e i) := by
      rw [hfirst, hsecond, Finset.sum_add_distrib]
    _ = (n - 1 : Nat) * ∑ i, e i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      push_cast
      have hi := i.isLt
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      ring

theorem centered_root_difference
    {m a b : Nat} (hm : 0 < m) :
    Complex.exp (-Complex.I *
          (Real.pi * ((a + b : Nat) : Real) / (m : Real))) *
        (Complex.exp (Complex.I *
            (2 * Real.pi * (b : Real) / (m : Real))) -
          Complex.exp (Complex.I *
            (2 * Real.pi * (a : Real) / (m : Real)))) =
      (2 * Real.sin
          (Real.pi * ((b : Real) - a) / (m : Real)) : Real) *
        Complex.I := by
  have hmR : (m : Real) ≠ 0 := by exact_mod_cast hm.ne'
  let A : Real := Real.pi * a / m
  let B : Real := Real.pi * b / m
  have hcenter : Real.pi * ((a + b : Nat) : Real) / (m : Real) = A + B := by
    dsimp [A, B]
    push_cast
    field_simp [hmR]
  have ha : 2 * Real.pi * (a : Real) / (m : Real) = 2 * A := by
    dsimp [A]
    ring
  have hb : 2 * Real.pi * (b : Real) / (m : Real) = 2 * B := by
    dsimp [B]
    ring
  have hdiff : Real.pi * ((b : Real) - a) / (m : Real) = B - A := by
    dsimp [A, B]
    ring
  have hcenterC' :
      (Real.pi : Complex) * (((a + b : Nat) : Real) : Complex) /
          (((m : Nat) : Real) : Complex) =
        (A : Complex) + B := by
    exact_mod_cast hcenter
  have haC :
      (2 : Complex) * Real.pi * (((a : Nat) : Real) : Complex) /
          (((m : Nat) : Real) : Complex) = 2 * (A : Complex) := by
    exact_mod_cast ha
  have hbC :
      (2 : Complex) * Real.pi * (((b : Nat) : Real) : Complex) /
          (((m : Nat) : Real) : Complex) = 2 * (B : Complex) := by
    exact_mod_cast hb
  rw [hcenterC', haC, hbC, hdiff]
  rw [show (A : Complex) + B = ((A + B : Real) : Complex) by
    push_cast
    rfl]
  rw [show (2 : Complex) * B = ((2 * B : Real) : Complex) by
    push_cast
    rfl]
  rw [show (2 : Complex) * A = ((2 * A : Real) : Complex) by
    push_cast
    rfl]
  rw [show -Complex.I * ((A + B : Real) : Complex) =
      (-(A + B : Real) : Complex) * Complex.I by push_cast; ring]
  rw [show Complex.I * ((2 * B : Real) : Complex) =
      ((2 * B : Real) : Complex) * Complex.I by ring]
  rw [show Complex.I * ((2 * A : Real) : Complex) =
      ((2 * A : Real) : Complex) * Complex.I by ring]
  rw [← Complex.ofReal_neg]
  simp only [Complex.exp_ofReal_mul_I]
  rw [Real.cos_neg, Real.sin_neg]
  rw [Real.cos_add, Real.sin_add]
  rw [Real.cos_two_mul, Real.sin_two_mul, Real.cos_two_mul, Real.sin_two_mul]
  rw [Real.sin_sub]
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re,
      Complex.ofReal_re, Complex.I_re, Complex.add_im, Complex.sub_im,
      Complex.mul_im, Complex.ofReal_im, Complex.I_im, mul_zero, mul_one,
      zero_mul, zero_add, add_zero, sub_zero, neg_mul]
  · ring_nf
    calc
      -(Real.cos A * Real.cos B * Real.sin A ^ 2 * 2) +
            Real.cos A * Real.cos B * Real.sin B ^ 2 * 2 +
            Real.cos A * Real.cos B ^ 3 * 2 -
          Real.cos A ^ 3 * Real.cos B * 2 =
          2 * Real.cos A * Real.cos B *
            ((Real.sin B ^ 2 + Real.cos B ^ 2) -
              (Real.sin A ^ 2 + Real.cos A ^ 2)) := by ring
      _ = 0 := by rw [Real.sin_sq_add_cos_sq, Real.sin_sq_add_cos_sq]; ring
  · ring_nf
    calc
      Real.cos A * Real.sin A ^ 2 * Real.sin B * 2 +
            Real.cos A ^ 3 * Real.sin B * 2 -
            Real.cos B * Real.sin A * Real.sin B ^ 2 * 2 -
          Real.cos B ^ 3 * Real.sin A * 2 =
          2 * Real.cos A * Real.sin B *
              (Real.sin A ^ 2 + Real.cos A ^ 2) -
            2 * Real.cos B * Real.sin A *
              (Real.sin B ^ 2 + Real.cos B ^ 2) := by ring
      _ = Real.cos A * Real.sin B * 2 -
          Real.cos B * Real.sin A * 2 := by
            rw [Real.sin_sq_add_cos_sq, Real.sin_sq_add_cos_sq]
            ring


end
end StatMech.FrontierD
