/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedEntropy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.PBiasedTensorize.Part11
import Def.StatisticalMechanics.Code.Probability.PBiasedEntropy
open scoped BigOperators
open Finset
open Real

set_option linter.style.longLine false


namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem pen_dampedMass_nonneg {p r : ℝ} (hr : 0 ≤ r) (f : ConfigSpace ι → ℝ) :
    0 ≤ pen_dampedMass p r f := by
  unfold pen_dampedMass
  exact Finset.sum_nonneg (fun S _ => by positivity)


theorem pen_dampedMass_pos {p r : ℝ} (hr : 0 < r) (f : ConfigSpace ι → ℝ)
    (hV : 0 < ∑ S ∈ (univ.erase (∅ : Finset ι)), (ptn_coeff p f S) ^ 2) :
    0 < pen_dampedMass p r f := by
  unfold pen_dampedMass
  
  by_contra hle
  rw [not_lt] at hle
  have hnn : ∀ S ∈ (univ.erase (∅ : Finset ι)), 0 ≤ (ptn_coeff p f S) ^ 2 * r ^ S.card :=
    fun S _ => by positivity
  have heq : ∑ S ∈ (univ.erase (∅ : Finset ι)), (ptn_coeff p f S) ^ 2 * r ^ S.card = 0 :=
    le_antisymm hle (Finset.sum_nonneg hnn)
  rw [Finset.sum_eq_zero_iff_of_nonneg hnn] at heq
  
  have hVzero : ∑ S ∈ (univ.erase (∅ : Finset ι)), (ptn_coeff p f S) ^ 2 = 0 := by
    apply Finset.sum_eq_zero
    intro S hS
    have := heq S hS
    have hrpos : 0 < r ^ S.card := by positivity
    nlinarith [this, hrpos, sq_nonneg (ptn_coeff p f S)]
  rw [hVzero] at hV
  exact lt_irrefl 0 hV


omit [Fintype ι] [DecidableEq ι] in


theorem pen_degree_extraction {κ : Type*} (s : Finset κ) (c : κ → ℝ) (d : κ → ℕ) (r : ℝ)
    (hr0 : 0 < r) (hc : ∀ k ∈ s, 0 ≤ c k)
    (hD : 0 < ∑ k ∈ s, c k * r ^ (d k)) :
    (∑ k ∈ s, c k) * Real.log ((∑ k ∈ s, c k) / (∑ k ∈ s, c k * r ^ (d k)))
      ≤ Real.log (1 / r) * ∑ k ∈ s, (d k : ℝ) * c k := by
  set D := ∑ k ∈ s, c k * r ^ (d k) with hDdef
  set V := ∑ k ∈ s, c k with hVdef
  set w : κ → ℝ := fun k => c k * r ^ (d k) / D with hw
  set t : κ → ℝ := fun k => r ^ (-(d k : ℝ)) with ht
  have hconv := convexOn_mul_log
  have hw0 : ∀ k ∈ s, 0 ≤ w k := by
    intro k hk; rw [hw]; apply div_nonneg _ (le_of_lt hD)
    exact mul_nonneg (hc k hk) (by positivity)
  have hwsum : ∑ k ∈ s, w k = 1 := by
    rw [hw, ← Finset.sum_div, div_self (ne_of_gt hD)]
  have hmem : ∀ k ∈ s, t k ∈ Set.Ici (0 : ℝ) := by
    intro k _; rw [ht]; simp only [Set.mem_Ici]; positivity
  have hJ := hconv.map_sum_le hw0 hwsum hmem
  have hsmul1 : ∑ k ∈ s, w k • t k = V / D := by
    rw [hVdef, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    simp only [smul_eq_mul, hw, ht]
    rw [div_mul_eq_mul_div]
    congr 1
    rw [mul_assoc, show r ^ (d k) * r ^ (-(d k : ℝ)) = (1:ℝ) from ?_]
    · ring
    · rw [← Real.rpow_natCast r (d k), ← Real.rpow_add hr0]; simp
  have hsmul2 : ∑ k ∈ s, w k • ((fun x => x * Real.log x) (t k))
      = (Real.log (1 / r) / D) * ∑ k ∈ s, (d k : ℝ) * c k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [smul_eq_mul, hw, ht]
    have hlog : Real.log (r ^ (-(d k : ℝ))) = (d k : ℝ) * Real.log (1 / r) := by
      rw [Real.log_rpow hr0, Real.log_div one_ne_zero (ne_of_gt hr0), Real.log_one, zero_sub]
      ring
    rw [hlog,
      show (c k * r ^ (d k) / D) * (r ^ (-(d k : ℝ)) * ((d k : ℝ) * Real.log (1/r)))
        = (Real.log (1/r) / D) * ((d k : ℝ) * c k) * (r ^ (d k) * r ^ (-(d k : ℝ))) from by ring,
      show r ^ (d k) * r ^ (-(d k : ℝ)) = (1:ℝ) from ?_]
    · ring
    · rw [← Real.rpow_natCast r (d k), ← Real.rpow_add hr0]; simp
  rw [hsmul1, hsmul2] at hJ
  have hkey := mul_le_mul_of_nonneg_left hJ (le_of_lt hD)
  rw [show D * ((V / D) * Real.log (V / D)) = V * Real.log (V / D) from by field_simp,
    show D * (Real.log (1 / r) / D * ∑ k ∈ s, (d k : ℝ) * c k)
      = Real.log (1 / r) * ∑ k ∈ s, (d k : ℝ) * c k from by field_simp] at hkey
  exact hkey


theorem pen_logGain_assembly {V D T δ L pp M : ℝ}
    (hV : 0 < V) (hD : 0 < D) (hT : 0 ≤ T) (hδ : 0 ≤ δ) (hpp : 0 ≤ pp)
    (hM : M = pp * T)
    (Hext : V * Real.log (V / D) ≤ L * M)
    (Hdamp : D ≤ δ * V)
    (Hlog : 4 * pp * L ≤ 2) :
    2 * V * Real.log (1 / δ) ≤ T := by
  rcases le_or_gt 1 δ with hδ1 | hδ1
  · have hlogle : Real.log (1 / δ) ≤ 0 := by
      rw [Real.log_div one_ne_zero (by linarith), Real.log_one, zero_sub, neg_nonpos]
      exact Real.log_nonneg (by linarith)
    nlinarith [hlogle, hV, hT]
  · rcases eq_or_lt_of_le hδ with hδ0 | hδ0
    · rw [← hδ0, div_zero, Real.log_zero, mul_zero]; exact hT
    · have hineq : 1 / δ ≤ V / D := by
        rw [div_le_div_iff₀ hδ0 hD]; nlinarith [Hdamp]
      have hlogmono : Real.log (1 / δ) ≤ Real.log (V / D) :=
        Real.log_le_log (by positivity) hineq
      have h2 : V * Real.log (1 / δ) ≤ L * M :=
        le_trans (mul_le_mul_of_nonneg_left hlogmono (le_of_lt hV)) Hext
      have hppL : pp * L ≤ 1 / 2 := by nlinarith [Hlog]
      have h3 : L * M ≤ (1/2) * T := by rw [hM]; nlinarith [hppL, hT, hpp]
      nlinarith [h2, h3]


theorem pen_degreeWeight_eq {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (φ : ConfigSpace ι → Bool) :
    (∑ S ∈ (univ.erase (∅ : Finset ι)),
        (S.card : ℝ) * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      = p * (1 - p) * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  
  have hfull : (∑ S ∈ (univ.erase (∅ : Finset ι)),
        (S.card : ℝ) * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      = ∑ S : Finset ι, (S.card : ℝ) * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 := by
    rw [← Finset.add_sum_erase univ
        (fun S => (S.card : ℝ) * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
        (Finset.mem_univ ∅)]
    simp
  rw [hfull, ptn_totalInfl_eq_fourierWeight hp0 hp1 φ, ptn_sigma_sq hp0 hp1]
  have hpne : (p : ℝ) ≠ 0 := ne_of_gt hp0
  have h1pne : (1 - p : ℝ) ≠ 0 := by have : 0 < 1 - p := by linarith
                                     exact ne_of_gt this
  field_simp


end StatMech.Probability
