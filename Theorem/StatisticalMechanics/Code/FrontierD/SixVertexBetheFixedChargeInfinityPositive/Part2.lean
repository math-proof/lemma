/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeInfinityPositive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeInfinityNonzero
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeInfinityPositive
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFixedChargeLimitingCenterProduct_eq_pairProduct
    (r k : Nat)
    (x : SixVertexSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k)) :
    (∏ i, sixVertexFixedChargeLimitingPhaseCenter r k ^
        sixVertexFixedChargeAlternantExponent r k x i) =
      ∏ i, ∏ j ∈ Finset.Ioi i,
        Complex.exp (-Complex.I *
          (Real.pi *
            ((sixVertexFixedChargeAlternantExponent r k x i +
              sixVertexFixedChargeAlternantExponent r k x j : Nat) : Real) /
            (sixVertexFixedChargeBetheComplementCount r k : Real))) := by
  let n := sixVertexFixedChargeBetheParticleCount r k
  let m := sixVertexFixedChargeBetheComplementCount r k
  let e := sixVertexFixedChargeAlternantExponent r k x
  simp_rw [sixVertexFixedChargeLimitingPhaseCenter, ← Complex.exp_nat_mul]
  rw [← Complex.exp_sum]
  simp_rw [← Complex.exp_sum]
  congr 1
  have hm : (m : Real) ≠ 0 := by
    exact_mod_cast (sixVertexFixedChargeBetheComplementCount_pos r k).ne'
  have hsum := sum_Ioi_pair_add (fun i => (e i : Real))
  dsimp only [n, m, e] at hsum
  have hsumC := congrArg (fun t : Real => (t : Complex)) hsum
  push_cast at hsumC
  calc
    (∑ i, (sixVertexFixedChargeAlternantExponent r k x i : Complex) *
        (-Complex.I *
          (Real.pi *
            (sixVertexFixedChargeBetheParticleCount r k - 1 : Nat) /
              (sixVertexFixedChargeBetheComplementCount r k : Real)))) =
      (-Complex.I *
          (Real.pi / (sixVertexFixedChargeBetheComplementCount r k : Real))) *
        (((sixVertexFixedChargeBetheParticleCount r k - 1 : Nat) : Complex) *
          ∑ i, (sixVertexFixedChargeAlternantExponent r k x i : Complex)) := by
            rw [← Finset.sum_mul]
            push_cast
            ring
    _ = (-Complex.I *
          (Real.pi / (sixVertexFixedChargeBetheComplementCount r k : Real))) *
        (∑ i, ∑ j ∈ Finset.Ioi i,
          ((sixVertexFixedChargeAlternantExponent r k x i : Complex) +
            (sixVertexFixedChargeAlternantExponent r k x j : Complex))) := by
              rw [hsumC]
    _ = ∑ i, ∑ j ∈ Finset.Ioi i,
        -Complex.I *
          (Real.pi *
            ((sixVertexFixedChargeAlternantExponent r k x i +
              sixVertexFixedChargeAlternantExponent r k x j : Nat) : Real) /
            (sixVertexFixedChargeBetheComplementCount r k : Real)) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              push_cast
              field_simp [hm]

theorem sixVertexFixedChargeLimitingWave_eq_phase_mul_sineProduct
    (r k : Nat)
    (x : SixVertexSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k)) :
    sixVertexFixedChargeLimitingWave r k x =
      Complex.I ^ sixVertexFixedChargeBethePairCount r k *
        sixVertexFixedChargeLimitingSineProduct r k x := by
  rw [sixVertexFixedChargeLimitingWave_eq_center_mul_vandermonde,
    Matrix.det_vandermonde,
    sixVertexFixedChargeLimitingCenterProduct_eq_pairProduct]
  have hIpow : Complex.I ^ sixVertexFixedChargeBethePairCount r k =
      ∏ i : Fin (sixVertexFixedChargeBetheParticleCount r k),
        ∏ _j ∈ Finset.Ioi i, Complex.I := by
    unfold sixVertexFixedChargeBethePairCount
    rw [← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_congr rfl
    intro i _
    rw [Finset.prod_const]
  rw [hIpow]
  have hsineCast :
      (sixVertexFixedChargeLimitingSineProduct r k x : Complex) =
        ∏ i, ∏ j ∈ Finset.Ioi i,
          ((2 * Real.sin
            (Real.pi *
              ((sixVertexFixedChargeAlternantExponent r k x j : Real) -
                sixVertexFixedChargeAlternantExponent r k x i) /
              (sixVertexFixedChargeBetheComplementCount r k : Real)) : Real) :
            Complex) := by
    unfold sixVertexFixedChargeLimitingSineProduct
    rw [Complex.ofReal_prod]
    apply Finset.prod_congr rfl
    intro i _
    rw [Complex.ofReal_prod]
  rw [hsineCast]
  conv_lhs => rw [← Finset.prod_mul_distrib]
  conv_rhs => rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  conv_lhs => rw [← Finset.prod_mul_distrib]
  conv_rhs => rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  have hm := sixVertexFixedChargeBetheComplementCount_pos r k
  simp_rw [sixVertexFixedChargeAlternantPoint,
    sixVertexFixedChargeLimitingPhaseStep, ← Complex.exp_nat_mul]
  rw [show (sixVertexFixedChargeAlternantExponent r k x j : Complex) *
        (Complex.I *
          (2 * Real.pi /
            (sixVertexFixedChargeBetheComplementCount r k : Real))) =
      Complex.I *
        (2 * Real.pi *
          (sixVertexFixedChargeAlternantExponent r k x j : Real) /
            (sixVertexFixedChargeBetheComplementCount r k : Real)) by
      push_cast
      ring]
  rw [show (sixVertexFixedChargeAlternantExponent r k x i : Complex) *
        (Complex.I *
          (2 * Real.pi /
            (sixVertexFixedChargeBetheComplementCount r k : Real))) =
      Complex.I *
        (2 * Real.pi *
          (sixVertexFixedChargeAlternantExponent r k x i : Real) /
            (sixVertexFixedChargeBetheComplementCount r k : Real)) by
      push_cast
      ring]
  rw [centered_root_difference hm]
  push_cast
  ring

theorem sixVertexFixedChargeLimitingSineProduct_pos_of_noAdjacent
    (r k : Nat)
    (x : SixVertexSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k))
    (hx : SixVertexSectorNoAdjacent x) :
    0 < sixVertexFixedChargeLimitingSineProduct r k x := by
  unfold sixVertexFixedChargeLimitingSineProduct
  apply Finset.prod_pos
  intro i _
  apply Finset.prod_pos
  intro j hj
  have hij : i < j := Finset.mem_Ioi.mp hj
  have heij :=
    strictMono_sixVertexFixedChargeAlternantExponent_of_noAdjacent r k x hx hij
  have heijR :
      (sixVertexFixedChargeAlternantExponent r k x i : Real) <
        (sixVertexFixedChargeAlternantExponent r k x j : Real) := by
    exact_mod_cast heij
  have hdiff : (0 : Real) <
      (sixVertexFixedChargeAlternantExponent r k x j : Real) -
        (sixVertexFixedChargeAlternantExponent r k x i : Real) := by
    linarith
  have hspan := sixVertexFixedChargeAlternantExponent_sub_abs_lt_complement
    r k x hx j i
  rw [abs_of_pos hdiff] at hspan
  have hm : (0 : Real) < sixVertexFixedChargeBetheComplementCount r k := by
    exact_mod_cast sixVertexFixedChargeBetheComplementCount_pos r k
  have harg0 : 0 < Real.pi *
      ((sixVertexFixedChargeAlternantExponent r k x j : Real) -
        sixVertexFixedChargeAlternantExponent r k x i) /
      (sixVertexFixedChargeBetheComplementCount r k : Real) := by
    exact div_pos (mul_pos Real.pi_pos hdiff) hm
  have hargpi : Real.pi *
      ((sixVertexFixedChargeAlternantExponent r k x j : Real) -
        sixVertexFixedChargeAlternantExponent r k x i) /
      (sixVertexFixedChargeBetheComplementCount r k : Real) < Real.pi := by
    apply (div_lt_iff₀ hm).2
    nlinarith [Real.pi_pos]
  exact mul_pos (by norm_num) (Real.sin_pos_of_pos_of_lt_pi harg0 hargpi)


theorem sixVertexFixedChargeLimitingWave_rotated_re_pos_of_noAdjacent
    (r k : Nat)
    (x : SixVertexSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k))
    (hx : SixVertexSectorNoAdjacent x) :
    0 < ((-Complex.I) ^
        sixVertexFixedChargeBethePairCount r k *
      sixVertexFixedChargeLimitingWave r k x).re := by
  rw [sixVertexFixedChargeLimitingWave_eq_phase_mul_sineProduct]
  rw [← mul_assoc, ← mul_pow]
  norm_num
  simpa using sixVertexFixedChargeLimitingSineProduct_pos_of_noAdjacent
    r k x hx

end
end StatMech.FrontierD
