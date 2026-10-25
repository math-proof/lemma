/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootBounds.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePerronBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexSelectedBetheM_norm_ge
    {c : Real} (hc : 2 < c) (k : Nat) (j : Fin (k + 1)) :
    (c ^ 2 - 2) / 2 ≤
      ‖sixVertexBetheM c
        (sixVertexBethePhase (sixVertexPositiveHalfBetheRoots hc k j))‖ := by
  let p := sixVertexPositiveHalfBetheRoots hc k j
  let q : Real := (c ^ 2 - 2) / 2
  let num : Real := (c ^ 2 - 1) ^ 2 + 1 +
    2 * (c ^ 2 - 1) * Real.cos p
  let den : Real := 2 - 2 * Real.cos p
  have hphase : sixVertexBethePhase p ≠ 1 := by
    exact sixVertexHalfFilledBetheRoots_phase_ne_one hc k
      (Fin.natAdd (k + 1) j)
  have hformula := sixVertexBetheM_phase_normSq c p hphase
  have hMne := sixVertexBetheM_phase_ne_zero hc p
  have hratioPos : 0 < num / den := by
    rw [← hformula]
    exact Complex.normSq_pos.mpr hMne
  have hden : 0 < den := by
    rcases (div_pos_iff.mp hratioPos) with h | h
    · exact h.2
    · have hnumNonneg : 0 ≤ num := by
        dsimp [num]
        have hcos := Real.neg_one_le_cos p
        have ha : 0 ≤ c ^ 2 - 1 := by nlinarith
        nlinarith [sq_nonneg (c ^ 2 - 2)]
      linarith
  have hdenLe : den ≤ 4 := by
    dsimp [den]
    linarith [Real.neg_one_le_cos p]
  have hq : 0 < q := by dsimp [q]; nlinarith
  have hnum : (c ^ 2 - 2) ^ 2 ≤ num := by
    dsimp [num]
    have hcos := Real.neg_one_le_cos p
    have ha : 0 < c ^ 2 - 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hcos ha.le]
  have hratio : q ^ 2 ≤ num / den := by
    calc
      q ^ 2 = (c ^ 2 - 2) ^ 2 / 4 := by dsimp [q]; ring
      _ ≤ (c ^ 2 - 2) ^ 2 / den := by
        exact div_le_div_of_nonneg_left (sq_nonneg (c ^ 2 - 2)) hden hdenLe
      _ ≤ num / den := by
        exact div_le_div_of_nonneg_right hnum hden.le
  rw [← hformula] at hratio
  rw [Complex.normSq_eq_norm_sq] at hratio
  change q ≤ ‖sixVertexBetheM c (sixVertexBethePhase p)‖
  nlinarith [norm_nonneg (sixVertexBetheM c (sixVertexBethePhase p))]

theorem sixVertexSelectedBetheM_log_norm_ge
    {c : Real} (hc : 2 < c) (k : Nat) (j : Fin (k + 1)) :
    Real.log ((c ^ 2 - 2) / 2) ≤
      Real.log ‖sixVertexBetheM c
        (sixVertexBethePhase (sixVertexPositiveHalfBetheRoots hc k j))‖ := by
  apply Real.log_le_log (by nlinarith)
  exact sixVertexSelectedBetheM_norm_ge hc k j


theorem sixVertexSelectedRootAverage_ge
    {c : Real} (hc : 2 < c) (k : Nat) :
    Real.log ((c ^ 2 - 2) / 2) / 2 ≤
      sixVertexSymmetricBetheRootAverage c
        (sixVertexPositiveHalfBetheRootFamily hc) k := by
  let b : Real := Real.log ((c ^ 2 - 2) / 2)
  have hsum : (k + 1 : Real) * b ≤
      ∑ j : Fin (k + 1), Real.log ‖sixVertexBetheM c
        (sixVertexBethePhase (sixVertexPositiveHalfBetheRoots hc k j))‖ := by
    calc
      (k + 1 : Real) * b = ∑ _j : Fin (k + 1), b := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro j hj
        exact sixVertexSelectedBetheM_log_norm_ge hc k j
  have hN : (0 : Real) < sixVertexFourWidth 0 k := by
    exact_mod_cast sixVertexFourWidth_pos 0 k
  unfold sixVertexSymmetricBetheRootAverage
    sixVertexPositiveHalfBetheRootFamily
  rw [le_div_iff₀ hN]
  dsimp [b] at hsum ⊢
  rw [sixVertexFourWidth]
  push_cast
  nlinarith


theorem sixVertexHalfFilledBetheCandidateRate_ge
    {c : Real} (hc : 2 < c) (k : Nat) :
    Real.log ((c ^ 2 - 2) / 2) / 2 ≤
      sixVertexHalfFilledBetheCandidateRate hc k := by
  rw [sixVertexHalfFilledBetheCandidateRate_eq_rootAverage]
  have havg := sixVertexSelectedRootAverage_ge hc k
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hN : (0 : Real) ≤ sixVertexFourWidth 0 k := by positivity
  have hterm : 0 ≤ Real.log 2 / (sixVertexFourWidth 0 k : Real) :=
    div_nonneg hlog hN
  linarith


theorem sixVertexSelectedBetheM_norm_le_quantile
    {c : Real} (hc : 2 < c) (k : Nat) (j : Fin (k + 1)) :
    ‖sixVertexBetheM c
        (sixVertexBethePhase (sixVertexPositiveHalfBetheRoots hc k j))‖ ≤
      c ^ 2 * (sixVertexFourWidth 0 k : Real) /
        (2 * (2 * (j : Real) + 1)) := by
  let p := sixVertexPositiveHalfBetheRoots hc k j
  let N : Real := sixVertexFourWidth 0 k
  let s : Real := 2 * (j : Real) + 1
  let num : Real := (c ^ 2 - 1) ^ 2 + 1 +
    2 * (c ^ 2 - 1) * Real.cos p
  let den : Real := 2 - 2 * Real.cos p
  have hp : 0 < p := sixVertexPositiveHalfBetheRoots_pos hc k j
  have hpPi : p < Real.pi := sixVertexPositiveHalfBetheRoots_lt_pi hc k j
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast sixVertexFourWidth_pos 0 k
  have hs : 0 < s := by dsimp [s]; positivity
  have hphase : sixVertexBethePhase p ≠ 1 :=
    sixVertexHalfFilledBetheRoots_phase_ne_one hc k
      (Fin.natAdd (k + 1) j)
  have hformula := sixVertexBetheM_phase_normSq c p hphase
  have hMne := sixVertexBetheM_phase_ne_zero hc p
  have hratioPos : 0 < num / den := by
    rw [← hformula]
    exact Complex.normSq_pos.mpr hMne
  have hden : 0 < den := by
    rcases (div_pos_iff.mp hratioPos) with h | h
    · exact h.2
    · have hnumNonneg : 0 ≤ num := by
        dsimp [num]
        have hcos := Real.neg_one_le_cos p
        have ha : 0 ≤ c ^ 2 - 1 := by nlinarith
        nlinarith [sq_nonneg (c ^ 2 - 2)]
      linarith
  have hnum : num ≤ c ^ 4 := by
    dsimp [num]
    have hcos := Real.cos_le_one p
    have ha : 0 < c ^ 2 - 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hcos ha.le]
  have habsp : |p| ≤ Real.pi := by
    rw [abs_of_pos hp]
    exact hpPi.le
  have hcos := Real.cos_le_one_sub_mul_cos_sq habsp
  have hdenP : 4 * p ^ 2 ≤ Real.pi ^ 2 * den := by
    have hcos' := mul_le_mul_of_nonneg_left hcos (sq_nonneg Real.pi)
    field_simp [Real.pi_ne_zero] at hcos'
    dsimp [den]
    nlinarith
  have hquant := sixVertexPositiveHalfBetheRoots_quantile_lower hc k j
  change Real.pi * s < N * p at hquant
  have hquantSq : Real.pi ^ 2 * s ^ 2 ≤ N ^ 2 * p ^ 2 := by
    have hleft : 0 ≤ Real.pi * s := by positivity
    have hright : 0 ≤ N * p := by positivity
    nlinarith [(sq_le_sq₀ hleft hright).2 hquant.le]
  have hdenQuant : 4 * s ^ 2 ≤ N ^ 2 * den := by
    have hpiSq : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
    have hNnonneg : 0 ≤ N ^ 2 := sq_nonneg N
    have hs1 := mul_le_mul_of_nonneg_left hdenP hNnonneg
    have hs2 := mul_le_mul_of_nonneg_left hquantSq (by norm_num : (0 : Real) ≤ 4)
    nlinarith
  have hratio : num / den ≤ (c ^ 2 * N / (2 * s)) ^ 2 := by
    rw [div_le_iff₀ hden]
    have hc4 : 0 ≤ c ^ 4 := by positivity
    have hscale := mul_le_mul_of_nonneg_left hdenQuant hc4
    have hsne : s ≠ 0 := hs.ne'
    have hNne : N ≠ 0 := hN.ne'
    calc
      num ≤ c ^ 4 := hnum
      _ ≤ (c ^ 2 * N / (2 * s)) ^ 2 * den := by
        field_simp [hsne, hNne] at hscale ⊢
        nlinarith
  rw [← hformula, Complex.normSq_eq_norm_sq] at hratio
  change ‖sixVertexBetheM c (sixVertexBethePhase p)‖ ≤
    c ^ 2 * N / (2 * s)
  have hright : 0 ≤ c ^ 2 * N / (2 * s) := by positivity
  nlinarith [norm_nonneg (sixVertexBetheM c (sixVertexBethePhase p))]


theorem sixVertexSelectedBetheM_log_norm_le_quantile
    {c : Real} (hc : 2 < c) (k : Nat) (j : Fin (k + 1)) :
    Real.log ‖sixVertexBetheM c
        (sixVertexBethePhase (sixVertexPositiveHalfBetheRoots hc k j))‖ ≤
      Real.log (c ^ 2 * (sixVertexFourWidth 0 k : Real) /
        (2 * (2 * (j : Real) + 1))) := by
  have hleft : 0 < ‖sixVertexBetheM c
      (sixVertexBethePhase (sixVertexPositiveHalfBetheRoots hc k j))‖ :=
    norm_pos_iff.mpr (sixVertexBetheM_phase_ne_zero hc _)
  exact Real.log_le_log hleft
    (sixVertexSelectedBetheM_norm_le_quantile hc k j)


end
end StatMech.FrontierD
