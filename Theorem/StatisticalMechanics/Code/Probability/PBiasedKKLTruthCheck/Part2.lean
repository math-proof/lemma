/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedKKLTruthCheck.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.SummedBKKKLClose
import Def.StatisticalMechanics.Code.Probability.PBiasedKKLTruthCheck
open scoped BigOperators
open Finset Real Set

set_option linter.style.longLine false


namespace StatMech.Probability

open StatMech StatMech.OSSS


@[simp] theorem pbkt_andF_ff : pbkt_andF (ctp_cfg false false) = 0 := by
  simp [pbkt_andF, pbkt_AND, ctp_cfg]

@[simp] theorem pbkt_andF_ft : pbkt_andF (ctp_cfg false true) = 0 := by
  simp [pbkt_andF, pbkt_AND, ctp_cfg]

@[simp] theorem pbkt_andF_tf : pbkt_andF (ctp_cfg true false) = 0 := by
  simp [pbkt_andF, pbkt_AND, ctp_cfg]

@[simp] theorem pbkt_andF_tt : pbkt_andF (ctp_cfg true true) = 1 := by
  simp [pbkt_andF, pbkt_AND, ctp_cfg]


theorem pbkt_AND_expect (p : ℝ) :
    OSSS.expect (OSSS.bernoulliWeight p) pbkt_andF = p ^ 2 := by
  rw [ctp_expect_fin2]
  simp only [pbkt_andF_ff, pbkt_andF_ft, pbkt_andF_tf, pbkt_andF_tt]
  ring


theorem pbkt_AND_var (p : ℝ) :
    OSSS.var (OSSS.bernoulliWeight p) pbkt_andF = (1 - p ^ 2) * p ^ 2 := by
  have h := mil_var_eq (p := p) pbkt_AND
  change OSSS.var (OSSS.bernoulliWeight p) pbkt_andF = _ at h
  have hf : (fun ω => if pbkt_AND ω then (1 : ℝ) else 0) = pbkt_andF := rfl
  rw [hf, pbkt_AND_expect] at h
  nlinarith


theorem pbkt_AND_infl0 (p : ℝ) :
    OSSS.infl (OSSS.bernoulliWeight p) pbkt_andF 0 = p := by
  unfold OSSS.infl
  rw [ctp_expect_fin2]
  have hopen : ∀ a b : Bool, StatMech.setOpen 0 (ctp_cfg a b) = ctp_cfg true b := by
    intro a b
    funext i
    fin_cases i <;> simp [StatMech.setOpen, ctp_cfg, Function.update]
  have hclosed : ∀ a b : Bool, StatMech.setClosed 0 (ctp_cfg a b) = ctp_cfg false b := by
    intro a b
    funext i
    fin_cases i <;> simp [StatMech.setClosed, ctp_cfg, Function.update]
  simp only [hopen, hclosed, pbkt_andF_ff, pbkt_andF_ft, pbkt_andF_tf, pbkt_andF_tt]
  ring


theorem pbkt_AND_infl1 (p : ℝ) :
    OSSS.infl (OSSS.bernoulliWeight p) pbkt_andF 1 = p := by
  unfold OSSS.infl
  rw [ctp_expect_fin2]
  have hopen : ∀ a b : Bool, StatMech.setOpen 1 (ctp_cfg a b) = ctp_cfg a true := by
    intro a b
    funext i
    fin_cases i <;> simp [StatMech.setOpen, ctp_cfg, Function.update]
  have hclosed : ∀ a b : Bool, StatMech.setClosed 1 (ctp_cfg a b) = ctp_cfg a false := by
    intro a b
    funext i
    fin_cases i <;> simp [StatMech.setClosed, ctp_cfg, Function.update]
  simp only [hopen, hclosed, pbkt_andF_ff, pbkt_andF_ft, pbkt_andF_tf, pbkt_andF_tt]
  ring


theorem pbkt_AND_totalInfl (p : ℝ) :
    totalInfl (OSSS.bernoulliWeight p) pbkt_andF = 2 * p := by
  unfold totalInfl
  rw [Fin.sum_univ_two, pbkt_AND_infl0, pbkt_AND_infl1]
  ring


theorem pbkt_AND_maxInfl (p : ℝ) :
    maxInfl (OSSS.bernoulliWeight p) pbkt_andF = p := by
  unfold maxInfl
  have hfun : OSSS.infl (OSSS.bernoulliWeight p) pbkt_andF = fun _ => p := by
    funext e
    fin_cases e
    · exact pbkt_AND_infl0 p
    · exact pbkt_AND_infl1 p
  rw [hfun]
  simp [Finset.sup'_const]


theorem pbkt_AND_kkl_two {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    2 * OSSS.var (OSSS.bernoulliWeight p) pbkt_andF
        * Real.log (1 / maxInfl (OSSS.bernoulliWeight p) pbkt_andF)
      ≤ totalInfl (OSSS.bernoulliWeight p) pbkt_andF := by
  rw [pbkt_AND_var, pbkt_AND_maxInfl, pbkt_AND_totalInfl]
  exact pbkt_twoBit_atom_numeric hp0 hp1


theorem pbkt_dictator_kkl_two {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    2 * OSSS.var (OSSS.bernoulliWeight p)
          (fun ω : ConfigSpace (Fin 1) => if ω 0 then (1 : ℝ) else 0)
        * Real.log (1 / maxInfl (OSSS.bernoulliWeight p)
          (fun ω : ConfigSpace (Fin 1) => if ω 0 then (1 : ℝ) else 0))
      ≤ totalInfl (OSSS.bernoulliWeight p)
          (fun ω : ConfigSpace (Fin 1) => if ω 0 then (1 : ℝ) else 0) := by
  rw [vgp_dictator_var hp0 hp1, vgp_dictator_maxInfl hp0 hp1,
    vgp_dictator_totalInfl hp0 hp1]
  norm_num

end StatMech.Probability
