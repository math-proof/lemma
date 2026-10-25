/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLLevel2Final.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.BKKKLLevel2Close
import Def.StatisticalMechanics.Code.Probability.BKKKLLevel2Final
open scoped BigOperators
open Finset
open Real Set

set_option linter.style.longLine false


namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem bkt2f_levelGe2_of_meanInfl {q : ℝ} (H : bkt2f_meanInflResidue q) :
    bkt2_levelGe2MasterResidue q := by
  intro p hp hp1 E _ _ _ φ u hu0 hu1
  have hp0 : 0 < p := by have := hp.1; linarith
  obtain ⟨u', hu'0, hlt, hcap, k, hk1, hbudget⟩ := H p hp hp1 φ u hu0 hu1
  refine ⟨k, hk1, ?_⟩
  
  have hFS := bkt2f_FS_highDegree hp0 hp1 φ hu1 hu'0 hlt hcap k
  
  exact le_trans hFS hbudget


theorem bkt2f_remaining_of_meanInfl {q : ℝ} (H : bkt2f_meanInflResidue q) :
    bkt2_RemainingGoal q :=
  bkt2c_remaining_of_levelGe2 (bkt2f_levelGe2_of_meanInfl H)


theorem bkt2f_master_of_meanInfl {q : ℝ} (H : bkt2f_meanInflResidue q) :
    pro_PBiasedMaster q :=
  bkt2_master_of_remaining (bkt2f_remaining_of_meanInfl H)


theorem bkt2f_rhoOptimise_of_meanInfl {q : ℝ} (H : bkt2f_meanInflResidue q) :
    ptn_RhoOptimise q :=
  bkt2_rhoOptimise_of_remaining (bkt2f_remaining_of_meanInfl H)


theorem bkt2f_meanInflResidue_c0 {p : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    {u : ℝ} (hu1 : u < 1) (hcap : 1 - 4 * p * (1 - p) < u)
    (hδ0 : 0 < (maxInfl (OSSS.bernoulliWeight p)
        (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0))
        ^ (u / (2 - u))) :
    ∃ u' : ℝ, 0 < u' ∧ u' < u ∧ 1 - u' ≤ 4 * p * (1 - p) ∧ ∃ k : ℕ, 1 ≤ k ∧
      (4 / (u - u'))
        * (ptn_qnorm p (1 + (1 - u') / (4 * p * (1 - p)))
            (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0)) ^ 2
        ≤ (4 * (ptn_sigma p) ^ 2)
            * ((maxInfl (OSSS.bernoulliWeight p)
                (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0))
                ^ (u / (2 - u))
              - (1 - u) ^ k)
            * totalInfl (OSSS.bernoulliWeight p)
                (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0)
          - 4 * ∑ S ∈ univ.filter (fun S : Finset E => S.card = 1),
              (ptn_coeff p (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0) S) ^ 2 := by
  have hp0 : 0 < p := by linarith
  set f0 : ConfigSpace E → Bool := fun _ => false with hf0
  set s := 4 * p * (1 - p) with hs
  have hs0 : 0 < s := by rw [hs]; nlinarith
  have hs1 : s < 1 := by
    rw [hs]; have hne : (1 - 2 * p) ≠ 0 := by intro h; nlinarith [h]
    nlinarith [sq_nonneg (1 - 2 * p), (pow_two_pos_of_ne_zero hne)]
  have h1ms : (0 : ℝ) < 1 - s := by linarith
  have hu0 : 0 < u := lt_trans h1ms hcap
  
  have h1u : (1 : ℝ) - u < 1 := by linarith
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (x := (maxInfl (OSSS.bernoulliWeight p)
      (fun ω => if f0 ω then (1 : ℝ) else 0)) ^ (u / (2 - u))) hδ0 h1u
  
  set u' : ℝ := ((1 - s) + u) / 2 with hu'
  have hu'pos : 0 < u' := by rw [hu']; linarith
  have hu'lt : u' < u := by rw [hu']; linarith
  have hu'cap : 1 - u' ≤ s := by rw [hu']; linarith
  refine ⟨u', hu'pos, hu'lt, by rw [hs] at hu'cap ⊢; linarith [hu'cap], k + 1, by omega, ?_⟩
  
  have hq'pos : (0 : ℝ) < 1 + (1 - u') / s := by
    have : 0 ≤ (1 - u') / s := by
      apply div_nonneg _ hs0.le; nlinarith [hu'cap, hs1]
    linarith
  have hf0zero : (fun ω => if f0 ω then (1 : ℝ) else 0) = (fun _ : ConfigSpace E => (0 : ℝ)) := by
    funext ω; rw [hf0]; simp
  have hμ0 : OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if f0 ω then (1 : ℝ) else 0) = 0 := by
    rw [hf0zero]; unfold OSSS.expect; simp
  have hlhs0 : (ptn_qnorm p (1 + (1 - u') / s)
      (fun ω => if f0 ω then (1 : ℝ) else 0)) ^ 2 = 0 := by
    rw [bkt2f_qnorm_indicator_sq hp0.le hp1.le hq'pos f0, hμ0]
    rw [Real.zero_rpow (by positivity)]
  rw [show (4 / (u - u'))
      * (ptn_qnorm p (1 + (1 - u') / (4 * p * (1 - p)))
          (fun ω => if f0 ω then (1 : ℝ) else 0)) ^ 2 = 0 from by rw [← hs, hlhs0]; ring]
  
  have hcoeff0 : ∀ S : Finset E, ptn_coeff p (fun ω => if f0 ω then (1 : ℝ) else 0) S = 0 := by
    intro S; rw [hf0zero]; unfold ptn_coeff OSSS.expect; simp
  have hz1 : (4 : ℝ) * ∑ S ∈ univ.filter (fun S : Finset E => S.card = 1),
      (ptn_coeff p (fun ω => if f0 ω then (1 : ℝ) else 0) S) ^ 2 = 0 := by
    rw [Finset.sum_eq_zero (fun S _ => by rw [hcoeff0]; ring), mul_zero]
  rw [hz1, sub_zero]
  
  have hmono : (1 - u) ^ (k + 1) ≤ (1 - u) ^ k :=
    pow_le_pow_of_le_one (by linarith) (by linarith) (by omega)
  apply mul_nonneg
  · apply mul_nonneg (by positivity)
    linarith [hk, hmono]
  · exact kkl_totalInfl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0.le hp1.le) _


theorem bkt2f_gap_vanishes_at_p_half {u : ℝ} (d : ℕ) :
    (1 - u) ^ (d - 1) - (((1 - u) * (4 * (1/2 : ℝ) * (1 - 1/2))) ^ (d - 1)) = 0 := by
  rw [bkt2_target_eq_damped_of_p_half d]; ring

end StatMech.Probability
