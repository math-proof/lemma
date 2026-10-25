/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLMeanInfl.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.BKKKLLevel2Final.Part2
import Def.StatisticalMechanics.Code.Probability.BKKKLMeanInfl
open scoped BigOperators
open Finset
open Real Set

set_option linter.style.longLine false


namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem mil_levelGe2_of_var {q : ℝ} (H : mil_VarScalarCore q) :
    bkt2_levelGe2MasterResidue q := by
  intro p hp hp1 E _ _ _ φ u hu0 hu1
  have hp0 : 0 < p := by have := hp.1; linarith
  obtain ⟨k, hk1, hvar⟩ := H p hp hp1 φ u hu0 hu1
  refine ⟨k, hk1, ?_⟩
  set μ := OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) with hμ
  have hge2 := mil_levelGe2_le_var hp0 hp1 φ hu0 hu1 k
  rw [← hμ] at hge2
  have hlvl1var := mil_level1_le_var hp0 hp1 φ
  rw [← hμ] at hlvl1var
  
  have h4lvl1 : 4 * ∑ S ∈ univ.filter (fun S : Finset E => S.card = 1),
      (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 ≤ 4 * (μ * (1 - μ)) :=
    mul_le_mul_of_nonneg_left hlvl1var (by norm_num)
  linarith [hge2, hvar, h4lvl1]


theorem mil_master_of_varScalar {q : ℝ} (H : mil_VarScalarCore q) :
    pro_PBiasedMaster q :=
  bkt2_master_of_levelGe2 (mil_levelGe2_of_var H)


theorem mil_rhoOptimise_of_varScalar {q : ℝ} (H : mil_VarScalarCore q) :
    ptn_RhoOptimise q :=
  pro_rhoOptimise_of_master (mil_master_of_varScalar H)


theorem mil_varScalarCore_c0 {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (hδ0 : 0 < (maxInfl (OSSS.bernoulliWeight p)
        (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0))
        ^ (u / (2 - u))) :
    ∃ k : ℕ, 1 ≤ k ∧
      4 * ((k : ℝ) + 1)
        * (OSSS.expect (OSSS.bernoulliWeight p)
              (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0)
            * (1 - OSSS.expect (OSSS.bernoulliWeight p)
                (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0)))
        ≤ (4 * (ptn_sigma p) ^ 2)
            * ((maxInfl (OSSS.bernoulliWeight p)
                (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0))
                ^ (u / (2 - u))
              - (1 - u) ^ k)
            * totalInfl (OSSS.bernoulliWeight p)
                (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0) := by
  set f0 : ConfigSpace E → Bool := fun _ => false with hf0
  
  have h1u : (1 : ℝ) - u < 1 := by linarith
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (x := (maxInfl (OSSS.bernoulliWeight p)
      (fun ω => if f0 ω then (1 : ℝ) else 0)) ^ (u / (2 - u))) hδ0 h1u
  refine ⟨k + 1, by omega, ?_⟩
  
  have hf0zero : (fun ω => if f0 ω then (1 : ℝ) else 0) = (fun _ : ConfigSpace E => (0 : ℝ)) := by
    funext ω; rw [hf0]; simp
  have hμ0 : OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if f0 ω then (1 : ℝ) else 0) = 0 := by
    rw [hf0zero]; unfold OSSS.expect; simp
  rw [hμ0]
  simp only [zero_mul, mul_zero, sub_zero]
  
  have hmono : (1 - u) ^ (k + 1) ≤ (1 - u) ^ k :=
    pow_le_pow_of_le_one (by linarith) (by linarith) (by omega)
  have hσ2nn : (0 : ℝ) ≤ 4 * (ptn_sigma p) ^ 2 := by positivity
  apply mul_nonneg
  · apply mul_nonneg hσ2nn
    linarith [hk, hmono]
  · exact kkl_totalInfl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0.le hp1.le) _

end StatMech.Probability
