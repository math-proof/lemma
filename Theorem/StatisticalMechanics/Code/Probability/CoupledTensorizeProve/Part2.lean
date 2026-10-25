/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/CoupledTensorizeProve.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.MasterFamilyProve2.Part2
import Def.StatisticalMechanics.Code.Probability.CoupledTensorizeProve.Part2
open scoped BigOperators
open Finset
open Real Set

set_option linter.style.longLine false


namespace StatMech.Probability

open StatMech StatMech.OSSS


@[simp] theorem ctp_f_ff : ctp_f (ctp_cfg false false) = 0 := by simp [ctp_f, ctp_OR, ctp_cfg]

@[simp] theorem ctp_f_ft : ctp_f (ctp_cfg false true) = 1 := by simp [ctp_f, ctp_OR, ctp_cfg]

@[simp] theorem ctp_f_tf : ctp_f (ctp_cfg true false) = 1 := by simp [ctp_f, ctp_OR, ctp_cfg]

@[simp] theorem ctp_f_tt : ctp_f (ctp_cfg true true) = 1 := by simp [ctp_f, ctp_OR, ctp_cfg]


theorem ctp_psi_eval (p : ℝ) (b : Bool) :
    ptn_psi p b = ((if b then (1:ℝ) else 0) - p) / ptn_sigma p := by
  unfold ptn_psi ptn_val; cases b <;> simp


theorem ctp_pchar_zero (p : ℝ) (ω : ConfigSpace (Fin 2)) :
    ptn_pchar p {0} ω = ptn_psi p (ω 0) := by
  unfold ptn_pchar; rw [Finset.prod_singleton]


theorem ctp_pchar_zeroone (p : ℝ) (ω : ConfigSpace (Fin 2)) :
    ptn_pchar p ({0, 1} : Finset (Fin 2)) ω = ptn_psi p (ω 0) * ptn_psi p (ω 1) := by
  unfold ptn_pchar
  rw [Finset.prod_insert (by decide), Finset.prod_singleton]


theorem ctp_coeff_zero_sq_div :
    (ptn_coeff (9/10 : ℝ) ctp_f {0} / ptn_sigma (9/10)) ^ 2 = 1 / 100 := by
  have hp0 : (0:ℝ) < 9/10 := by norm_num
  have hp1 : (9/10 : ℝ) < 1 := by norm_num
  have hσ2 : ptn_sigma (9/10 : ℝ) ^ 2 = (9/10) * (1 - 9/10) := ptn_sigma_sq hp0 hp1
  have hσpos : 0 < ptn_sigma (9/10 : ℝ) := ptn_sigma_pos hp0 hp1
  have hσne : ptn_sigma (9/10 : ℝ) ≠ 0 := hσpos.ne'
  
  have hc : ptn_coeff (9/10 : ℝ) ctp_f {0}
      = (9/1000 : ℝ) / ptn_sigma (9/10) := by
    unfold ptn_coeff
    rw [ctp_expect_fin2]
    simp only [ctp_pchar_zero, ctp_cfg_zero, ctp_f_ff, ctp_f_ft, ctp_f_tf, ctp_f_tt]
    rw [ctp_psi_eval, ctp_psi_eval]
    simp only [Bool.false_eq_true, if_false, if_true]
    field_simp
    ring
  rw [hc, div_div]
  rw [div_pow]
  rw [show (ptn_sigma (9/10 : ℝ) * ptn_sigma (9/10)) = ptn_sigma (9/10) ^ 2 by ring, hσ2]
  norm_num


theorem ctp_coeff_zeroone_sq_div :
    (ptn_coeff (9/10 : ℝ) ctp_f ({0,1} : Finset (Fin 2)) / ptn_sigma (9/10)) ^ 2 = 9 / 100 := by
  have hp0 : (0:ℝ) < 9/10 := by norm_num
  have hp1 : (9/10 : ℝ) < 1 := by norm_num
  have hσ2 : ptn_sigma (9/10 : ℝ) ^ 2 = (9/10) * (1 - 9/10) := ptn_sigma_sq hp0 hp1
  have hσpos : 0 < ptn_sigma (9/10 : ℝ) := ptn_sigma_pos hp0 hp1
  have hσne : ptn_sigma (9/10 : ℝ) ≠ 0 := hσpos.ne'
  
  have hc : ptn_coeff (9/10 : ℝ) ctp_f ({0,1} : Finset (Fin 2))
      = (-(81/10000) : ℝ) / ptn_sigma (9/10) ^ 2 := by
    unfold ptn_coeff
    rw [ctp_expect_fin2]
    simp only [ctp_pchar_zeroone, ctp_cfg_zero, ctp_cfg_one, ctp_f_ff, ctp_f_ft, ctp_f_tf,
      ctp_f_tt]
    rw [ctp_psi_eval, ctp_psi_eval]
    simp only [Bool.false_eq_true, if_false, if_true]
    rw [show ptn_sigma (9/10 : ℝ) ^ 2 = ptn_sigma (9/10) * ptn_sigma (9/10) by ring]
    field_simp
    ring
  rw [hc, div_div, div_pow]
  rw [show (ptn_sigma (9/10 : ℝ) ^ 2 * ptn_sigma (9/10)) ^ 2
      = (ptn_sigma (9/10 : ℝ) ^ 2) ^ 3 by ring, hσ2]
  norm_num


theorem ctp_OR_infl0 :
    OSSS.infl (OSSS.bernoulliWeight (9/10 : ℝ)) ctp_f 0 = 1 / 10 := by
  unfold OSSS.infl
  rw [ctp_expect_fin2]
  have hopen : ∀ a b : Bool, (StatMech.setOpen 0 (ctp_cfg a b)) = ctp_cfg true b := by
    intro a b; funext i; fin_cases i <;> simp [StatMech.setOpen, ctp_cfg, Function.update]
  have hclosed : ∀ a b : Bool, (StatMech.setClosed 0 (ctp_cfg a b)) = ctp_cfg false b := by
    intro a b; funext i; fin_cases i <;> simp [StatMech.setClosed, ctp_cfg, Function.update]
  simp only [hopen, hclosed, ctp_f_ff, ctp_f_ft, ctp_f_tf, ctp_f_tt]
  norm_num


theorem ctp_filter_mem0 :
    (univ.filter (fun S : Finset (Fin 2) => (0 : Fin 2) ∈ S))
      = {({0} : Finset (Fin 2)), ({0, 1} : Finset (Fin 2))} := by
  decide


theorem ctp_OR_lhs_eq :
    (∑ S ∈ univ.filter (fun S : Finset (Fin 2) => (0 : Fin 2) ∈ S),
        (1 - (1/2 : ℝ)) ^ (S.erase 0).card
          * (ptn_coeff (9/10 : ℝ) ctp_f S / ptn_sigma (9/10)) ^ 2)
      = 11 / 200 := by
  rw [ctp_filter_mem0]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  
  rw [show (({0} : Finset (Fin 2)).erase 0).card = 0 by decide,
      show (({0, 1} : Finset (Fin 2)).erase 0).card = 1 by decide]
  rw [ctp_coeff_zero_sq_div, ctp_coeff_zeroone_sq_div]
  norm_num


theorem ctp_rhs_lt_lhs : ((1:ℝ) / 10) ^ ((4:ℝ) / 3) < 11 / 200 := by
  have hy : (0:ℝ) ≤ (11:ℝ) / 200 := by norm_num
  have hcube_x : (((1:ℝ) / 10) ^ ((4:ℝ) / 3)) ^ (3:ℕ) = ((1:ℝ) / 10) ^ (4:ℝ) := by
    rw [← Real.rpow_natCast (((1:ℝ) / 10) ^ ((4:ℝ) / 3)) 3, ← Real.rpow_mul (by norm_num)]
    norm_num
  have h10_4 : ((1:ℝ) / 10) ^ (4:ℝ) = 1 / 10000 := by
    rw [show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have hlt : (((1:ℝ) / 10) ^ ((4:ℝ) / 3)) ^ (3:ℕ) < ((11:ℝ) / 200) ^ (3:ℕ) := by
    rw [hcube_x, h10_4]; norm_num
  by_contra hc
  rw [not_lt] at hc
  exact absurd (pow_le_pow_left₀ hy hc 3) (not_le.mpr hlt)


theorem ctp_perCoordHighNoise_false {q : ℝ} (hq : (9 : ℝ) / 10 < q) :
    ¬ mfp2_PerCoordHighNoise q := by
  intro H
  have hp : (9/10 : ℝ) ∈ Set.Ioo (1/2 : ℝ) q := ⟨by norm_num, hq⟩
  have hp1 : (9/10 : ℝ) < 1 := by norm_num
  
  have h := H (9/10) hp hp1 ctp_OR (1/2) (by norm_num) (by norm_num) 0
  
  rw [show (fun ω => if ctp_OR ω then (1:ℝ) else 0) = ctp_f from rfl] at h
  rw [ctp_OR_lhs_eq, ctp_OR_infl0] at h
  
  rw [show (2:ℝ) / (2 - 1/2) = 4 / 3 by norm_num] at h
  exact absurd h (not_le.mpr ctp_rhs_lt_lhs)


theorem ctp_engine_holds_at_witness :
    (∑ S ∈ univ.filter (fun S : Finset (Fin 2) => (0 : Fin 2) ∈ S),
        (Real.sqrt ((3/2 - 1) * 4 * (9/10) * (1 - 9/10)) ^ (S.erase 0).card) ^ 2
          * (ptn_coeff (9/10 : ℝ) (fun ω => if ctp_OR ω then (1:ℝ) else 0) S
              / ptn_sigma (9/10)) ^ 2)
      ≤ (OSSS.infl (OSSS.bernoulliWeight (9/10 : ℝ))
          (fun ω => if ctp_OR ω then (1:ℝ) else 0) 0) ^ (2 / (3/2 : ℝ)) := by
  have hp0 : (0:ℝ) < 9/10 := by norm_num
  have hp1 : (9/10 : ℝ) < 1 := by norm_num
  set ρ := Real.sqrt ((3/2 - 1) * 4 * (9/10) * (1 - 9/10)) with hρ
  have hnn : (0:ℝ) ≤ (3/2 - 1) * 4 * (9/10) * (1 - 9/10) := by norm_num
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρ1 : ρ ≤ 1 := by
    rw [hρ]; apply Real.sqrt_le_one.mpr; norm_num
  have hρsq : ρ ^ 2 = (3/2 - 1) * 4 * (9/10) * (1 - 9/10) := by
    rw [hρ, Real.sq_sqrt hnn]
  exact ptn_perCoord_hc hp0 hp1 hρ0 hρ1 (by norm_num) (by norm_num) hρsq ctp_OR 0


theorem ctp_perCoordHighNoise_unsatisfiable_but_reduction_valid {q : ℝ} (hq : (9 : ℝ) / 10 < q) :
    (¬ mfp2_PerCoordHighNoise q)
      ∧ (mfp2_PerCoordHighNoise q → frh_openResidue q) :=
  ⟨ctp_perCoordHighNoise_false hq, mfp2_openResidue_of_perCoordHighNoise⟩


theorem ctp_half_holds_but_window_fails {q : ℝ} (hq : (9 : ℝ) / 10 < q) :
    (∀ {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (φ : ConfigSpace E → Bool)
        (u : ℝ), 0 < u → u < 1 → ∀ e : E,
        (∑ S ∈ univ.filter (fun S : Finset E => e ∈ S),
            (1 - u) ^ (S.erase e).card * (ptn_coeff (1/2 : ℝ) (fun ω => if φ ω then (1:ℝ) else 0) S
              / ptn_sigma (1/2)) ^ 2)
          ≤ (OSSS.infl (OSSS.bernoulliWeight (1/2 : ℝ))
              (fun ω => if φ ω then (1:ℝ) else 0) e) ^ (2 / (2 - u)))
      ∧ ¬ mfp2_PerCoordHighNoise q :=
  ⟨fun φ _u hu0 hu1 e => mfp2_perCoordHighNoise_half φ hu0 hu1 e,
    ctp_perCoordHighNoise_false hq⟩

end StatMech.Probability
