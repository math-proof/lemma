/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterTwoBondUpper.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterSingleBondUpper.Part2
import Theorem.StatisticalMechanics.Code.Ising.GHSInhomogeneous.Part11
import Theorem.StatisticalMechanics.Code.Sharpness.Simon.Part3
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterTwoBondUpper
open Set
open scoped BigOperators


namespace StatMech.Ising

noncomputable section

open StatMech.Sharpness


theorem twoBond_skew_ratio_le_product
    {t a b e : Real}
    (ht0 : 0 <= t) (ht1 : t < 1)
    (ha0 : 0 <= a) (ha1 : a <= 1)
    (hb0 : 0 <= b) (hb1 : b <= 1)
    (he : a * b <= e) :
    (1 + t * (a + b) + t ^ 2 * e) /
        (1 - t * (a + b) + t ^ 2 * e) <=
      ((1 + t * a) / (1 - t * a)) *
        ((1 + t * b) / (1 - t * b)) := by
  have hta : 0 <= t * a := mul_nonneg ht0 ha0
  have htb : 0 <= t * b := mul_nonneg ht0 hb0
  have hta1 : t * a < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right ht0 ha1) ht1
  have htb1 : t * b < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right ht0 hb1) ht1
  have hda : 0 < 1 - t * a := sub_pos.mpr hta1
  have hdb : 0 < 1 - t * b := sub_pos.mpr htb1
  have hdprod : 0 < (1 - t * a) * (1 - t * b) := mul_pos hda hdb
  have ht2 : 0 <= t ^ 2 := sq_nonneg t
  have hdenLower :
      (1 - t * a) * (1 - t * b) <=
        1 - t * (a + b) + t ^ 2 * e := by
    have heTerm : t ^ 2 * (a * b) <= t ^ 2 * e :=
      mul_le_mul_of_nonneg_left he ht2
    nlinarith
  have hden : 0 < 1 - t * (a + b) + t ^ 2 * e :=
    hdprod.trans_le hdenLower
  have hbaseDen : 0 < 1 - t * (a + b) + t ^ 2 * (a * b) := by
    convert hdprod using 1 <;> ring
  have heTerm : t ^ 2 * (a * b) <= t ^ 2 * e :=
    mul_le_mul_of_nonneg_left he ht2
  have hmono :
      (1 + t * (a + b) + t ^ 2 * e) /
          (1 - t * (a + b) + t ^ 2 * e) <=
        (1 + t * (a + b) + t ^ 2 * (a * b)) /
          (1 - t * (a + b) + t ^ 2 * (a * b)) := by
    rw [div_le_div_iff₀ hden hbaseDen]
    nlinarith [mul_nonneg ht0 (add_nonneg ha0 hb0)]
  calc
    (1 + t * (a + b) + t ^ 2 * e) /
        (1 - t * (a + b) + t ^ 2 * e) <=
      (1 + t * (a + b) + t ^ 2 * (a * b)) /
        (1 - t * (a + b) + t ^ 2 * (a * b)) := hmono
    _ = ((1 + t * a) / (1 - t * a)) *
        ((1 + t * b) / (1 - t * b)) := by
      rw [show 1 + t * (a + b) + t ^ 2 * (a * b) =
          (1 + t * a) * (1 + t * b) by ring,
        show 1 - t * (a + b) + t ^ 2 * (a * b) =
          (1 - t * a) * (1 - t * b) by ring,
        mul_div_mul_comm]


theorem twoBondInterfaceFreeEnergy_le
    {K m1 m2 c : Real} (hK : 0 <= K)
    (hm10 : 0 <= m1) (hm11 : m1 <= 1)
    (hm20 : 0 <= m2) (hm21 : m2 <= 1)
    (hc0 : 0 <= c) (hc1 : c <= 1)
    (hgks : m1 * m2 <= c) :
    twoBondInterfaceFreeEnergy K m1 m2 c <=
      2 * K * (m1 ^ 2 + m2 ^ 2) := by
  let t := Real.tanh K
  let a := m1 ^ 2
  let b := m2 ^ 2
  let e := c ^ 2
  have ht0 : 0 <= t := by
    dsimp [t]
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr hK) (Real.cosh_pos K).le
  have ht1 : t < 1 := Real.tanh_lt_one K
  have ha0 : 0 <= a := sq_nonneg m1
  have ha1 : a <= 1 := by nlinarith
  have hb0 : 0 <= b := sq_nonneg m2
  have hb1 : b <= 1 := by nlinarith
  have he0 : 0 <= e := sq_nonneg c
  have he1 : e <= 1 := by nlinarith
  have hab : a * b <= e := by
    dsimp [a, b, e]
    have hs := mul_self_le_mul_self (mul_nonneg hm10 hm20) hgks
    nlinarith
  have hratio := twoBond_skew_ratio_le_product
    ht0 ht1 ha0 ha1 hb0 hb1 hab
  have hda : 0 < 1 - t * a := by
    apply sub_pos.mpr
    exact lt_of_le_of_lt (mul_le_of_le_one_right ht0 ha1) ht1
  have hdb : 0 < 1 - t * b := by
    apply sub_pos.mpr
    exact lt_of_le_of_lt (mul_le_of_le_one_right ht0 hb1) ht1
  have hfa :
      Real.log ((1 + t * a) / (1 - t * a)) <= 2 * K * a := by
    simpa [singleBondInterfaceFreeEnergy, t, mul_comm] using
      (singleBondInterfaceFreeEnergy_le hK ha0 ha1 zero_le_one le_rfl)
  have hfb :
      Real.log ((1 + t * b) / (1 - t * b)) <= 2 * K * b := by
    simpa [singleBondInterfaceFreeEnergy, t, mul_comm] using
      (singleBondInterfaceFreeEnergy_le hK hb0 hb1 zero_le_one le_rfl)
  have hrightPosA : 0 < (1 + t * a) / (1 - t * a) :=
    div_pos (by nlinarith [mul_nonneg ht0 ha0]) hda
  have hrightPosB : 0 < (1 + t * b) / (1 - t * b) :=
    div_pos (by nlinarith [mul_nonneg ht0 hb0]) hdb
  have hleftDen : 0 < 1 - t * (a + b) + t ^ 2 * e := by
    have hp : 0 < (1 - t * a) * (1 - t * b) := mul_pos hda hdb
    have heTerm : t ^ 2 * (a * b) <= t ^ 2 * e :=
      mul_le_mul_of_nonneg_left hab (sq_nonneg t)
    nlinarith
  have hleftPos : 0 <
      (1 + t * (a + b) + t ^ 2 * e) /
        (1 - t * (a + b) + t ^ 2 * e) := by
    apply div_pos
    · nlinarith [mul_nonneg ht0 (add_nonneg ha0 hb0),
        mul_nonneg (sq_nonneg t) he0]
    · exact hleftDen
  have hlog := Real.log_le_log hleftPos hratio
  rw [Real.log_mul hrightPosA.ne' hrightPosB.ne'] at hlog
  unfold twoBondInterfaceFreeEnergy
  dsimp only
  change Real.log ((1 + t * (a + b) + t ^ 2 * e) /
      (1 - t * (a + b) + t ^ 2 * e)) <= 2 * K * (a + b)
  linarith


end
end StatMech.Ising
