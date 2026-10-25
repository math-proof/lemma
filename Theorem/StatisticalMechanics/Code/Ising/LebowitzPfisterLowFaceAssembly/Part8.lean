/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeEndpointZero
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterLowFaceCertificate
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterLowFaceAssembly.Part8
open Finset


namespace StatMech.Ising

open StatMech.FrontierA

open StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace LowFaceCertificate

lemma bernsteinAverageSeven_eq_quadraticAverage
    (x : Real) (f : Fin 8 -> Real)
    (hquad : ∀ i : Fin 8,
      f i = f 0 + i.val * (f 1 - f 0) +
        i.val.choose 2 * (f 2 - 2 * f 1 + f 0)) :
    bernsteinAverageSeven x f = quadraticAverage x f := by
  have hlin := bernsteinAverageSeven_natCast_mul x (f 1 - f 0)
  have hquad' := bernsteinAverageSeven_choose_two_mul x
    (f 2 - 2 * f 1 + f 0)
  calc
    bernsteinAverageSeven x f = bernsteinAverageSeven x
        (fun i => f 0 + i.val * (f 1 - f 0) +
          i.val.choose 2 * (f 2 - 2 * f 1 + f 0)) := by
      apply congrArg (bernsteinAverageSeven x)
      funext i
      exact hquad i
    _ = bernsteinAverageSeven x (fun _ => f 0) +
          bernsteinAverageSeven x (fun i => i.val * (f 1 - f 0)) +
          bernsteinAverageSeven x
            (fun i => i.val.choose 2 * (f 2 - 2 * f 1 + f 0)) := by
      rw [bernsteinAverageSeven_add, bernsteinAverageSeven_add]
    _ = f 0 + (f 1 - f 0) * (7 * x) +
          (f 2 - 2 * f 1 + f 0) * (21 * x ^ 2) := by
      rw [bernsteinAverageSeven_const,
        show bernsteinAverageSeven x (fun i => i.val * (f 1 - f 0)) =
          bernsteinAverageSeven x (fun i => (f 1 - f 0) * i.val) by
            apply congrArg (bernsteinAverageSeven x)
            funext i
            ring,
        hlin,
        show bernsteinAverageSeven x
            (fun i => i.val.choose 2 * (f 2 - 2 * f 1 + f 0)) =
          bernsteinAverageSeven x
            (fun i => (f 2 - 2 * f 1 + f 0) * i.val.choose 2) by
              apply congrArg (bernsteinAverageSeven x)
              funext i
              ring,
        hquad']
    _ = quadraticAverage x f := by
      unfold quadraticAverage
      ring

lemma quadraticAverage_preserves_quadratic
    (x : Real) (F : Fin 8 -> Fin 8 -> Real)
    (hquad : ∀ (i j : Fin 8),
      F i j = F 0 j + i.val * (F 1 j - F 0 j) +
        i.val.choose 2 * (F 2 j - 2 * F 1 j + F 0 j))
    (i : Fin 8) :
    quadraticAverage x (fun j => F i j) =
      quadraticAverage x (fun j => F 0 j) +
        i.val * (quadraticAverage x (fun j => F 1 j) -
          quadraticAverage x (fun j => F 0 j)) +
        i.val.choose 2 * (quadraticAverage x (fun j => F 2 j) -
          2 * quadraticAverage x (fun j => F 1 j) +
          quadraticAverage x (fun j => F 0 j)) := by
  unfold quadraticAverage
  simp only
  rw [hquad i 0, hquad i 1, hquad i 2]
  norm_num [Nat.choose]
  ring

set_option maxHeartbeats 10000000 in
theorem crossNumerator_bernstein_average
    (x y z a b c : Real) :
    bernsteinAverageSeven a (fun i =>
      bernsteinAverageSeven b (fun j =>
        bernsteinAverageSeven c (fun k =>
          (crossCoeffPoly i j k).eval x y z))) =
      1764 * crossNumerator x y z a b c := by
  let f : Fin 8 -> Fin 8 -> Fin 8 -> Real := fun i j k =>
    (crossCoeffPoly i j k).eval x y z
  have hf_k (i j k : Fin 8) :
      f i j k = f i j 0 + k.val * (f i j 1 - f i j 0) +
        k.val.choose 2 * (f i j 2 - 2 * f i j 1 + f i j 0) := by
    dsimp [f]
    simp only [eval_crossCoeffPoly]
    fin_cases k <;> norm_num [Nat.choose] <;> ring
  have hf_j (i j k : Fin 8) :
      f i j k = f i 0 k + j.val * (f i 1 k - f i 0 k) +
        j.val.choose 2 * (f i 2 k - 2 * f i 1 k + f i 0 k) := by
    dsimp [f]
    simp only [eval_crossCoeffPoly]
    fin_cases j <;> norm_num [Nat.choose] <;> ring
  have hf_i (i j k : Fin 8) :
      f i j k = f 0 j k + i.val * (f 1 j k - f 0 j k) +
        i.val.choose 2 * (f 2 j k - 2 * f 1 j k + f 0 j k) := by
    dsimp [f]
    simp only [eval_crossCoeffPoly]
    fin_cases i <;> norm_num [Nat.choose] <;> ring
  have hk (i j : Fin 8) :
      bernsteinAverageSeven c (fun k => f i j k) =
        quadraticAverage c (fun k => f i j k) := by
    apply bernsteinAverageSeven_eq_quadraticAverage
    exact hf_k i j
  have hj (i : Fin 8) :
      bernsteinAverageSeven b (fun j =>
        quadraticAverage c (fun k => f i j k)) =
      quadraticAverage b (fun j =>
        quadraticAverage c (fun k => f i j k)) := by
    apply bernsteinAverageSeven_eq_quadraticAverage
    intro j
    exact quadraticAverage_preserves_quadratic c
      (fun j k => f i j k) (hf_j i) j
  have hi :
      bernsteinAverageSeven a (fun i =>
        quadraticAverage b (fun j => quadraticAverage c (fun k => f i j k))) =
      quadraticAverage a (fun i =>
        quadraticAverage b (fun j => quadraticAverage c (fun k => f i j k))) := by
    apply bernsteinAverageSeven_eq_quadraticAverage
    intro i
    exact quadraticAverage_preserves_quadratic b
      (fun i j => quadraticAverage c (fun k => f i j k))
      (fun i j => quadraticAverage_preserves_quadratic c
        (fun i k => f i j k) (fun i k => hf_i i j k) i) i
  calc
    bernsteinAverageSeven a (fun i =>
        bernsteinAverageSeven b (fun j =>
          bernsteinAverageSeven c (fun k =>
            (crossCoeffPoly i j k).eval x y z))) =
      bernsteinAverageSeven a (fun i =>
        bernsteinAverageSeven b (fun j =>
          quadraticAverage c (fun k => f i j k))) := by
        apply congrArg (bernsteinAverageSeven a)
        funext i
        apply congrArg (bernsteinAverageSeven b)
        funext j
        exact hk i j
    _ = bernsteinAverageSeven a (fun i =>
        quadraticAverage b (fun j => quadraticAverage c (fun k => f i j k))) := by
      apply congrArg (bernsteinAverageSeven a)
      funext i
      exact hj i
    _ = quadraticAverage a (fun i =>
        quadraticAverage b (fun j => quadraticAverage c (fun k => f i j k))) := hi
    _ = 1764 * crossNumerator x y z a b c := by
      dsimp [quadraticAverage, f, crossNumerator]
      simp only [eval_crossCoeffPoly]
      norm_num
      ring

set_option maxHeartbeats 1000000 in
theorem crossCoeffPoly_eval_nonneg_ordered
    (i j k : Fin 8) {x y z : Real}
    (hx : 0 < x) (hxy : x <= y) (hyz : y <= z)
    (hsum : x + y + z <= 1) :
    0 <= (crossCoeffPoly i j k).eval x y z := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hz : 0 < z := lt_of_lt_of_le hy hyz
  let r := x / y
  let q := y / z
  let h := x + y + z
  have hr0 : 0 <= r := by positivity
  have hr1 : r <= 1 := (div_le_one hy).mpr hxy
  have hq0 : 0 <= q := by positivity
  have hq1 : q <= 1 := (div_le_one hz).mpr hyz
  have hh0 : 0 <= h := by dsimp [h]; positivity
  have hh1 : h <= 1 := hsum
  have hrad := radializedCrossCoeff_eval_nonneg i j k r q h
    hr0 hr1 hq0 hq1 hh0 hh1
  have hrqz : r * q * z = x := by
    dsimp [r, q]
    field_simp
  have hqz : q * z = y := by
    dsimp [q]
    field_simp
  have hzh : z * (1 + q + r * q) = h := by
    dsimp [r, q, h]
    field_simp
    ring
  have hd : 0 < 1 + q + r * q := by positivity
  have hp := TriPoly.eval_nonneg_of_radialize_relation
    (crossCoeffPoly i j k) r q z (le_of_lt hz) hd
      (crossCoeff_bounds i j k) (by
      rw [hzh]
      exact hrad)
  rw [hrqz, hqz] at hp
  exact hp

theorem crossNumerator_nonneg_ordered
    {x y z a b c : Real}
    (hx : 0 < x) (hxy : x <= y) (hyz : y <= z)
    (hsum : x + y + z <= 1)
    (ha0 : 0 <= a) (ha1 : a <= 1)
    (hb0 : 0 <= b) (hb1 : b <= 1)
    (hc0 : 0 <= c) (hc1 : c <= 1) :
    0 <= crossNumerator x y z a b c := by
  have havg : 0 <= bernsteinAverageSeven a (fun i =>
      bernsteinAverageSeven b (fun j =>
        bernsteinAverageSeven c (fun k =>
          (crossCoeffPoly i j k).eval x y z))) := by
    unfold bernsteinAverageSeven
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (bernsteinWeight_nonneg ha0 ha1) <| by
      apply Finset.sum_nonneg
      intro j _
      exact mul_nonneg (bernsteinWeight_nonneg hb0 hb1) <| by
        apply Finset.sum_nonneg
        intro k _
        exact mul_nonneg (bernsteinWeight_nonneg hc0 hc1)
          (crossCoeffPoly_eval_nonneg_ordered i j k hx hxy hyz hsum)
  rw [crossNumerator_bernstein_average] at havg
  nlinarith

set_option maxHeartbeats 1600000 in
theorem fourBridge_triangle_cross_remainder_nonneg_ordered_of_caps
    {x y z a b c : Real}
    (hx : 0 < x) (hxy : x <= y) (hyz : y <= z)
    (hsum : x ^ 2 + y ^ 2 + z ^ 2 <= 1)
    (ha : 0 <= a) (hb : 0 <= b) (hc : 0 <= c)
    (hacap : y * a <= (1 - y ^ 2) * x)
    (hbcap : z * b <= (1 - z ^ 2) * x)
    (hccap : z * c <= (1 - z ^ 2) * y) :
    0 <=
      x ^ 2 * (1 - x ^ 4) + y ^ 2 * (1 - y ^ 4) +
        z ^ 2 * (1 - z ^ 4) +
      9 * (a * x * y * (x ^ 2 + y ^ 2) +
        b * x * z * (x ^ 2 + z ^ 2) +
        c * y * z * (y ^ 2 + z ^ 2)) +
      6 * x * a * b * (x * y * z + y * b + z * a) +
      6 * y * a * c * (x * y * z + x * c + z * a) +
      6 * z * b * c * (x * y * z + x * c + y * b) -
      9 * (a * b * y * z + a * c * x * z + b * c * x * y) := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hz : 0 < z := lt_of_lt_of_le hy hyz
  have hx2 : 0 < x ^ 2 := sq_pos_of_pos hx
  have hy2 : 0 < y ^ 2 := sq_pos_of_pos hy
  have hz2 : 0 < z ^ 2 := sq_pos_of_pos hz
  have hyv : 0 < 1 - y ^ 2 := by nlinarith [hz2]
  have hzv : 0 < 1 - z ^ 2 := by nlinarith [hx2]
  let A := y * a / ((1 - y ^ 2) * x)
  let B := z * b / ((1 - z ^ 2) * x)
  let C := z * c / ((1 - z ^ 2) * y)
  have hA0 : 0 <= A := by dsimp [A]; positivity
  have hA1 : A <= 1 := by
    dsimp [A]
    exact (div_le_one (mul_pos hyv hx)).mpr hacap
  have hB0 : 0 <= B := by dsimp [B]; positivity
  have hB1 : B <= 1 := by
    dsimp [B]
    exact (div_le_one (mul_pos hzv hx)).mpr hbcap
  have hC0 : 0 <= C := by dsimp [C]; positivity
  have hC1 : C <= 1 := by
    dsimp [C]
    exact (div_le_one (mul_pos hzv hy)).mpr hccap
  have hXY : x ^ 2 <= y ^ 2 := by nlinarith
  have hYZ : y ^ 2 <= z ^ 2 := by nlinarith
  have hcert := crossNumerator_nonneg_ordered
    (x := x ^ 2) (y := y ^ 2) (z := z ^ 2)
    (a := A) (b := B) (c := C)
    hx2 hXY hYZ hsum hA0 hA1 hB0 hB1 hC0 hC1
  have hid :
      crossNumerator (x ^ 2) (y ^ 2) (z ^ 2) A B C =
      y ^ 2 * z ^ 2 *
        (x ^ 2 * (1 - x ^ 4) + y ^ 2 * (1 - y ^ 4) +
          z ^ 2 * (1 - z ^ 4) +
        9 * (a * x * y * (x ^ 2 + y ^ 2) +
          b * x * z * (x ^ 2 + z ^ 2) +
          c * y * z * (y ^ 2 + z ^ 2)) +
        6 * x * a * b * (x * y * z + y * b + z * a) +
        6 * y * a * c * (x * y * z + x * c + z * a) +
        6 * z * b * c * (x * y * z + x * c + y * b) -
        9 * (a * b * y * z + a * c * x * z + b * c * x * y)) := by
    dsimp [A, B, C, crossNumerator]
    field_simp
    ring
  rw [hid] at hcert
  exact nonneg_of_mul_nonneg_left (by simpa [mul_comm] using hcert)
    (mul_pos hy2 hz2)

set_option maxHeartbeats 1200000 in
theorem fourBridge_triangle_cross_remainder_nonneg_of_sqsum_le_one
    {x y z a b c : Real}
    (hx0 : 0 <= x) (hy0 : 0 <= y) (hz0 : 0 <= z)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hx1 : x <= 1) (hy1 : y <= 1) (hz1 : z <= 1)
    (ha : 0 <= a) (hb : 0 <= b) (hc : 0 <= c)
    (hxa : x * a ^ 2 <= (1 - x ^ 2) * y * a)
    (hya : y * a ^ 2 <= (1 - y ^ 2) * x * a)
    (hxb : x * b ^ 2 <= (1 - x ^ 2) * z * b)
    (hzb : z * b ^ 2 <= (1 - z ^ 2) * x * b)
    (hyc : y * c ^ 2 <= (1 - y ^ 2) * z * c)
    (hzc : z * c ^ 2 <= (1 - z ^ 2) * y * c)
    (hsum : x ^ 2 + y ^ 2 + z ^ 2 <= 1) :
    0 <=
      x ^ 2 * (1 - x ^ 4) + y ^ 2 * (1 - y ^ 4) +
        z ^ 2 * (1 - z ^ 4) +
      9 * (a * x * y * (x ^ 2 + y ^ 2) +
        b * x * z * (x ^ 2 + z ^ 2) +
        c * y * z * (y ^ 2 + z ^ 2)) +
      6 * x * a * b * (x * y * z + y * b + z * a) +
      6 * y * a * c * (x * y * z + x * c + z * a) +
      6 * z * b * c * (x * y * z + x * c + y * b) -
      9 * (a * b * y * z + a * c * x * z + b * c * x * y) := by
  have gxa := pair_covariance_square_bound_cancel hx0 hy0 hx1 ha hxa
  have gya := pair_covariance_square_bound_cancel hy0 hx0 hy1 ha hya
  have gxb := pair_covariance_square_bound_cancel hx0 hz0 hx1 hb hxb
  have gzb := pair_covariance_square_bound_cancel hz0 hx0 hz1 hb hzb
  have gyc := pair_covariance_square_bound_cancel hy0 hz0 hy1 hc hyc
  have gzc := pair_covariance_square_bound_cancel hz0 hy0 hz1 hc hzc
  rcases le_total x y with hxy | hyx
  · rcases le_total y z with hyz | hzy
    · exact fourBridge_triangle_cross_remainder_nonneg_ordered_of_caps
        hx hxy hyz hsum ha hb hc gya gzb gzc
    · rcases le_total x z with hxz | hzx
      · have h := fourBridge_triangle_cross_remainder_nonneg_ordered_of_caps
          hx hxz hzy (by nlinarith : x ^ 2 + z ^ 2 + y ^ 2 <= 1)
          hb ha hc gzb gya gyc
        convert h using 1 <;> ring
      · have h := fourBridge_triangle_cross_remainder_nonneg_ordered_of_caps
          hz hzx hxy (by nlinarith : z ^ 2 + x ^ 2 + y ^ 2 <= 1)
          hb hc ha gxb gyc gya
        convert h using 1 <;> ring
  · rcases le_total x z with hxz | hzx
    · have h := fourBridge_triangle_cross_remainder_nonneg_ordered_of_caps
        hy hyx hxz (by nlinarith : y ^ 2 + x ^ 2 + z ^ 2 <= 1)
        ha hc hb gxa gzc gzb
      convert h using 1 <;> ring
    · rcases le_total y z with hyz | hzy
      · have h := fourBridge_triangle_cross_remainder_nonneg_ordered_of_caps
          hy hyz hzx (by nlinarith : y ^ 2 + z ^ 2 + x ^ 2 <= 1)
          hc ha hb gzc gxa gxb
        convert h using 1 <;> ring
      · have h := fourBridge_triangle_cross_remainder_nonneg_ordered_of_caps
          hz hzy hyx (by nlinarith : z ^ 2 + y ^ 2 + x ^ 2 <= 1)
          hc hb ha gyc gxb gxa
        convert h using 1 <;> ring

theorem fourBridge_triangle_correct_nonneg_of_sqsum_le_one
    {x y z a b c : Real}
    (hx0 : 0 <= x) (hy0 : 0 <= y) (hz0 : 0 <= z)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hx1 : x <= 1) (hy1 : y <= 1) (hz1 : z <= 1)
    (ha : 0 <= a) (hb : 0 <= b) (hc : 0 <= c)
    (hxa : x * a ^ 2 <= (1 - x ^ 2) * y * a)
    (hya : y * a ^ 2 <= (1 - y ^ 2) * x * a)
    (hxb : x * b ^ 2 <= (1 - x ^ 2) * z * b)
    (hzb : z * b ^ 2 <= (1 - z ^ 2) * x * b)
    (hyc : y * c ^ 2 <= (1 - y ^ 2) * z * c)
    (hzc : z * c ^ 2 <= (1 - z ^ 2) * y * c)
    (hsum : x ^ 2 + y ^ 2 + z ^ 2 <= 1) :
    0 <=
      x ^ 2 * (1 - x ^ 4) + y ^ 2 * (1 - y ^ 4) +
        z ^ 2 * (1 - z ^ 4) +
      9 * (a * x * y * (x ^ 2 + y ^ 2) +
        b * x * z * (x ^ 2 + z ^ 2) +
        c * y * z * (y ^ 2 + z ^ 2)) +
      9 / 2 * (a ^ 2 * (x ^ 2 + y ^ 2) +
        b ^ 2 * (x ^ 2 + z ^ 2) + c ^ 2 * (y ^ 2 + z ^ 2)) +
      (-18 * a * b * y * z +
        6 * x * a * b * (x * y * z + y * b + z * a)) +
      (-18 * a * c * x * z +
        6 * y * a * c * (x * y * z + x * c + z * a)) +
      (-18 * b * c * x * y +
        6 * z * b * c * (x * y * z + x * c + y * b)) := by
  have hcross := fourBridge_triangle_cross_remainder_nonneg_of_sqsum_le_one
    hx0 hy0 hz0 hx hy hz hx1 hy1 hz1 ha hb hc
    hxa hya hxb hzb hyc hzc hsum
  have hsquares : 0 <= 9 / 2 *
      ((y * a - z * b) ^ 2 + (x * a - z * c) ^ 2 +
        (x * b - y * c) ^ 2) := by positivity
  have hid :
      a ^ 2 * (x ^ 2 + y ^ 2) + b ^ 2 * (x ^ 2 + z ^ 2) +
          c ^ 2 * (y ^ 2 + z ^ 2) -
          2 * (a * b * y * z + a * c * x * z + b * c * x * y) =
        (y * a - z * b) ^ 2 + (x * a - z * c) ^ 2 +
          (x * b - y * c) ^ 2 := by ring
  nlinarith [hid]

theorem fourBridge_triangle_correct_nonneg
    {x y z a b c : Real}
    (hx0 : 0 <= x) (hy0 : 0 <= y) (hz0 : 0 <= z)
    (hx1 : x <= 1) (hy1 : y <= 1) (hz1 : z <= 1)
    (ha : 0 <= a) (hb : 0 <= b) (hc : 0 <= c)
    (hxa : x * a ^ 2 <= (1 - x ^ 2) * y * a)
    (hya : y * a ^ 2 <= (1 - y ^ 2) * x * a)
    (hxb : x * b ^ 2 <= (1 - x ^ 2) * z * b)
    (hzb : z * b ^ 2 <= (1 - z ^ 2) * x * b)
    (hyc : y * c ^ 2 <= (1 - y ^ 2) * z * c)
    (hzc : z * c ^ 2 <= (1 - z ^ 2) * y * c) :
    0 <=
      x ^ 2 * (1 - x ^ 4) + y ^ 2 * (1 - y ^ 4) +
        z ^ 2 * (1 - z ^ 4) +
      9 * (a * x * y * (x ^ 2 + y ^ 2) +
        b * x * z * (x ^ 2 + z ^ 2) +
        c * y * z * (y ^ 2 + z ^ 2)) +
      9 / 2 * (a ^ 2 * (x ^ 2 + y ^ 2) +
        b ^ 2 * (x ^ 2 + z ^ 2) + c ^ 2 * (y ^ 2 + z ^ 2)) +
      (-18 * a * b * y * z +
        6 * x * a * b * (x * y * z + y * b + z * a)) +
      (-18 * a * c * x * z +
        6 * y * a * c * (x * y * z + x * c + z * a)) +
      (-18 * b * c * x * y +
        6 * z * b * c * (x * y * z + x * c + y * b)) := by
  by_cases hzero : x = 0 ∨ y = 0 ∨ z = 0
  · exact fourBridge_triangle_correct_nonneg_of_any_eq_zero
      hx0 hy0 hz0 hx1 hy1 hz1 ha hb hc
      hxa hya hxb hzb hyc hzc hzero
  · have hx : 0 < x := lt_of_le_of_ne hx0 (by tauto)
    have hy : 0 < y := lt_of_le_of_ne hy0 (by tauto)
    have hz : 0 < z := lt_of_le_of_ne hz0 (by tauto)
    rcases le_total 1 (x ^ 2 + y ^ 2 + z ^ 2) with hhigh | hlow
    · exact fourBridge_triangle_correct_nonneg_of_sqsum_ge_one
        hx0 hy0 hz0 hx1 hy1 hz1 ha hb hc
        hxa hya hxb hzb hyc hzc hhigh
    · exact fourBridge_triangle_correct_nonneg_of_sqsum_le_one
        hx0 hy0 hz0 hx hy hz hx1 hy1 hz1 ha hb hc
        hxa hya hxb hzb hyc hzc hlow

set_option maxHeartbeats 1600000 in
theorem fourBridge_Ursell_correction_nonneg
    {m0 m1 m2 m3 c01 c02 c03 c12 c13 c23 : Real}
    (hm00 : 0 <= m0) (hm10 : 0 <= m1) (hm20 : 0 <= m2) (hm30 : 0 <= m3)
    (hm01 : m0 <= 1) (hm11 : m1 <= 1) (hm21 : m2 <= 1) (hm31 : m3 <= 1)
    (hc01 : 0 <= c01) (hc02 : 0 <= c02) (hc03 : 0 <= c03)
    (hc12 : 0 <= c12) (hc13 : 0 <= c13) (hc23 : 0 <= c23)
    (h001 : m0 * c01 ^ 2 <= (1 - m0 ^ 2) * m1 * c01)
    (h101 : m1 * c01 ^ 2 <= (1 - m1 ^ 2) * m0 * c01)
    (h002 : m0 * c02 ^ 2 <= (1 - m0 ^ 2) * m2 * c02)
    (h202 : m2 * c02 ^ 2 <= (1 - m2 ^ 2) * m0 * c02)
    (h003 : m0 * c03 ^ 2 <= (1 - m0 ^ 2) * m3 * c03)
    (h303 : m3 * c03 ^ 2 <= (1 - m3 ^ 2) * m0 * c03)
    (h112 : m1 * c12 ^ 2 <= (1 - m1 ^ 2) * m2 * c12)
    (h212 : m2 * c12 ^ 2 <= (1 - m2 ^ 2) * m1 * c12)
    (h113 : m1 * c13 ^ 2 <= (1 - m1 ^ 2) * m3 * c13)
    (h313 : m3 * c13 ^ 2 <= (1 - m3 ^ 2) * m1 * c13)
    (h223 : m2 * c23 ^ 2 <= (1 - m2 ^ 2) * m3 * c23)
    (h323 : m3 * c23 ^ 2 <= (1 - m3 ^ 2) * m2 * c23) :
    let p01 := m0 * m1 + c01
    let p02 := m0 * m2 + c02
    let p03 := m0 * m3 + c03
    let p12 := m1 * m2 + c12
    let p13 := m1 * m3 + c13
    let p23 := m2 * m3 + c23
    let u012 := m0 * p12 + m1 * p02 + m2 * p01 - 2 * m0 * m1 * m2
    let u013 := m0 * p13 + m1 * p03 + m3 * p01 - 2 * m0 * m1 * m3
    let u023 := m0 * p23 + m2 * p03 + m3 * p02 - 2 * m0 * m2 * m3
    let u123 := m1 * p23 + m2 * p13 + m3 * p12 - 2 * m1 * m2 * m3
    let aa := m0 ^ 2 + m1 ^ 2 + m2 ^ 2 + m3 ^ 2
    let bb := p01 ^ 2 + p02 ^ 2 + p03 ^ 2 +
      p12 ^ 2 + p13 ^ 2 + p23 ^ 2
    0 <= aa + 3 * aa * bb - aa ^ 3 -
        3 * (u012 ^ 2 + u013 ^ 2 + u023 ^ 2 + u123 ^ 2) +
      2 * (m0 * c01 * c02 *
          (m0 * m1 * m2 + m1 * c02 + m2 * c01) +
        m1 * c01 * c12 *
          (m0 * m1 * m2 + m0 * c12 + m2 * c01) +
        m2 * c02 * c12 *
          (m0 * m1 * m2 + m0 * c12 + m1 * c02)) +
      2 * (m0 * c01 * c03 *
          (m0 * m1 * m3 + m1 * c03 + m3 * c01) +
        m1 * c01 * c13 *
          (m0 * m1 * m3 + m0 * c13 + m3 * c01) +
        m3 * c03 * c13 *
          (m0 * m1 * m3 + m0 * c13 + m1 * c03)) +
      2 * (m0 * c02 * c03 *
          (m0 * m2 * m3 + m2 * c03 + m3 * c02) +
        m2 * c02 * c23 *
          (m0 * m2 * m3 + m0 * c23 + m3 * c02) +
        m3 * c03 * c23 *
          (m0 * m2 * m3 + m0 * c23 + m2 * c03)) +
      2 * (m1 * c12 * c13 *
          (m1 * m2 * m3 + m2 * c13 + m3 * c12) +
        m2 * c12 * c23 *
          (m1 * m2 * m3 + m1 * c23 + m3 * c12) +
        m3 * c13 * c23 *
          (m1 * m2 * m3 + m1 * c23 + m2 * c13)) := by
  have h012 := fourBridge_triangle_correct_nonneg
    hm00 hm10 hm20 hm01 hm11 hm21 hc01 hc02 hc12
    h001 h101 h002 h202 h112 h212
  have h013 := fourBridge_triangle_correct_nonneg
    hm00 hm10 hm30 hm01 hm11 hm31 hc01 hc03 hc13
    h001 h101 h003 h303 h113 h313
  have h023 := fourBridge_triangle_correct_nonneg
    hm00 hm20 hm30 hm01 hm21 hm31 hc02 hc03 hc23
    h002 h202 h003 h303 h223 h323
  have h123 := fourBridge_triangle_correct_nonneg
    hm10 hm20 hm30 hm11 hm21 hm31 hc12 hc13 hc23
    h112 h212 h113 h313 h223 h323
  have hbase := fourBridge_zero_base_identity
    m0 m1 m2 m3 c01 c02 c03 c12 c13 c23
  dsimp at hbase ⊢
  rw [hbase]
  nlinarith

set_option maxHeartbeats 6000000 in
theorem fourBridgeVarianceSkewBernsteinCoeff_zero_nonpos
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V -> Real) (hf : V -> Real)
    (hK : forall e, 0 <= K e) (hhf : forall v, 0 <= hf v)
    {w x y z : V}
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    fourBridgeVarianceSkewBernsteinCoeff
        (fourBridgeOneCoeff G K hf w x y z)
        (fourBridgeTwoCoeff G K hf w x y z)
        (fourBridgeThreeCoeff G K hf w x y z)
        (fourBridgeFourCoeff G K hf w x y z) 0 <= 0 := by
  let m0 := grahamInhomOne G K hf w
  let m1 := grahamInhomOne G K hf x
  let m2 := grahamInhomOne G K hf y
  let m3 := grahamInhomOne G K hf z
  let c01 := ghsiCovariance G K hf w x
  let c02 := ghsiCovariance G K hf w y
  let c03 := ghsiCovariance G K hf w z
  let c12 := ghsiCovariance G K hf x y
  let c13 := ghsiCovariance G K hf x z
  let c23 := ghsiCovariance G K hf y z
  have hm00 := grahamInhomOne_nonneg G K hf hK hhf w
  have hm10 := grahamInhomOne_nonneg G K hf hK hhf x
  have hm20 := grahamInhomOne_nonneg G K hf hK hhf y
  have hm30 := grahamInhomOne_nonneg G K hf hK hhf z
  have hm01 := grahamInhomOne_le_one G K hf w
  have hm11 := grahamInhomOne_le_one G K hf x
  have hm21 := grahamInhomOne_le_one G K hf y
  have hm31 := grahamInhomOne_le_one G K hf z
  have hc01 := grahamInhomCov_nonneg G K hf hK hhf w x
  have hc02 := grahamInhomCov_nonneg G K hf hK hhf w y
  have hc03 := grahamInhomCov_nonneg G K hf hK hhf w z
  have hc12 := grahamInhomCov_nonneg G K hf hK hhf x y
  have hc13 := grahamInhomCov_nonneg G K hf hK hhf x z
  have hc23 := grahamInhomCov_nonneg G K hf hK hhf y z
  have h001 := grahamInhom_pair_covariance_square_le G K hf hK hhf w x
  have h101 := grahamInhom_pair_covariance_square_le G K hf hK hhf x w
  have h002 := grahamInhom_pair_covariance_square_le G K hf hK hhf w y
  have h202 := grahamInhom_pair_covariance_square_le G K hf hK hhf y w
  have h003 := grahamInhom_pair_covariance_square_le G K hf hK hhf w z
  have h303 := grahamInhom_pair_covariance_square_le G K hf hK hhf z w
  have h112 := grahamInhom_pair_covariance_square_le G K hf hK hhf x y
  have h212 := grahamInhom_pair_covariance_square_le G K hf hK hhf y x
  have h113 := grahamInhom_pair_covariance_square_le G K hf hK hhf x z
  have h313 := grahamInhom_pair_covariance_square_le G K hf hK hhf z x
  have h223 := grahamInhom_pair_covariance_square_le G K hf hK hhf y z
  have h323 := grahamInhom_pair_covariance_square_le G K hf hK hhf z y
  rw [ghsiCovariance_comm G K hf x w] at h101
  rw [ghsiCovariance_comm G K hf y w] at h202
  rw [ghsiCovariance_comm G K hf z w] at h303
  rw [ghsiCovariance_comm G K hf y x] at h212
  rw [ghsiCovariance_comm G K hf z x] at h313
  rw [ghsiCovariance_comm G K hf z y] at h323
  have hscalar := fourBridge_Ursell_correction_nonneg
    (m0 := m0) (m1 := m1) (m2 := m2) (m3 := m3)
    (c01 := c01) (c02 := c02) (c03 := c03)
    (c12 := c12) (c13 := c13) (c23 := c23)
    hm00 hm10 hm20 hm30 hm01 hm11 hm21 hm31
    hc01 hc02 hc03 hc12 hc13 hc23
    h001 h101 h002 h202 h003 h303 h112 h212 h113 h313 h223 h323
  have hcorr012 := grahamInhomThreePoint_square_correction_le
    G K hf hK hhf hwx hwy hxy
  have hcorr013 := grahamInhomThreePoint_square_correction_le
    G K hf hK hhf hwx hwz hxz
  have hcorr023 := grahamInhomThreePoint_square_correction_le
    G K hf hK hhf hwy hwz hyz
  have hcorr123 := grahamInhomThreePoint_square_correction_le
    G K hf hK hhf hxy hxz hyz
  have hp01 : expJ G.edgeFinset K hf (fun s => spin s w * spin s x) =
      m0 * m1 + c01 := by
    dsimp [m0, m1, c01]
    unfold grahamInhomOne ghsiCovariance
    ring
  have hp02 : expJ G.edgeFinset K hf (fun s => spin s w * spin s y) =
      m0 * m2 + c02 := by
    dsimp [m0, m2, c02]
    unfold grahamInhomOne ghsiCovariance
    ring
  have hp03 : expJ G.edgeFinset K hf (fun s => spin s w * spin s z) =
      m0 * m3 + c03 := by
    dsimp [m0, m3, c03]
    unfold grahamInhomOne ghsiCovariance
    ring
  have hp12 : expJ G.edgeFinset K hf (fun s => spin s x * spin s y) =
      m1 * m2 + c12 := by
    dsimp [m1, m2, c12]
    unfold grahamInhomOne ghsiCovariance
    ring
  have hp13 : expJ G.edgeFinset K hf (fun s => spin s x * spin s z) =
      m1 * m3 + c13 := by
    dsimp [m1, m3, c13]
    unfold grahamInhomOne ghsiCovariance
    ring
  have hp23 : expJ G.edgeFinset K hf (fun s => spin s y * spin s z) =
      m2 * m3 + c23 := by
    dsimp [m2, m3, c23]
    unfold grahamInhomOne ghsiCovariance
    ring
  have hone : fourBridgeOneCoeff G K hf w x y z =
      m0 ^ 2 + m1 ^ 2 + m2 ^ 2 + m3 ^ 2 := by
    unfold fourBridgeOneCoeff
    dsimp [m0, m1, m2, m3, grahamInhomOne]
  have htwo : fourBridgeTwoCoeff G K hf w x y z =
      (m0 * m1 + c01) ^ 2 + (m0 * m2 + c02) ^ 2 +
        (m0 * m3 + c03) ^ 2 + (m1 * m2 + c12) ^ 2 +
        (m1 * m3 + c13) ^ 2 + (m2 * m3 + c23) ^ 2 := by
    unfold fourBridgeTwoCoeff
    rw [hp01, hp02, hp03, hp12, hp13, hp23]
  have hthree : fourBridgeThreeCoeff G K hf w x y z =
      (expJ G.edgeFinset K hf
          (fun s => spin s w * (spin s x * spin s y))) ^ 2 +
        (expJ G.edgeFinset K hf
          (fun s => spin s w * (spin s x * spin s z))) ^ 2 +
        (expJ G.edgeFinset K hf
          (fun s => spin s w * (spin s y * spin s z))) ^ 2 +
        (expJ G.edgeFinset K hf
          (fun s => spin s x * (spin s y * spin s z))) ^ 2 := by
    rfl
  dsimp at hscalar hcorr012 hcorr013 hcorr023 hcorr123
  simp only [fourBridgeVarianceSkewBernsteinCoeff]
  rw [hone, htwo, hthree]
  dsimp [m0, m1, m2, m3, c01, c02, c03, c12, c13, c23]
  clear hm00 hm10 hm20 hm30 hm01 hm11 hm21 hm31
  clear hc01 hc02 hc03 hc12 hc13 hc23
  clear h001 h101 h002 h202 h003 h303 h112 h212 h113 h313 h223 h323
  clear hp01 hp02 hp03 hp12 hp13 hp23 hone htwo hthree
  linarith [hscalar, hcorr012, hcorr013, hcorr023, hcorr123]

end LowFaceCertificate
end
end StatMech.Ising
