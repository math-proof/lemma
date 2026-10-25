/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/EntropySubadditivity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.PBiasedEntropy.Part2
open scoped BigOperators
open Finset
open Real

set_option linter.style.longLine false


namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem esa_dampedMass_le {p r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (f : ConfigSpace ι → ℝ) :
    pen_dampedMass p r f
      ≤ r * (∑ S ∈ (univ.erase (∅ : Finset ι)), (ptn_coeff p f S) ^ 2) := by
  unfold pen_dampedMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro S hS
  have hScard : 1 ≤ S.card :=
    Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr (Finset.ne_of_mem_erase hS))
  have hrpow : r ^ S.card ≤ r := by
    calc r ^ S.card ≤ r ^ 1 := pow_le_pow_of_le_one hr0.le hr1 hScard
      _ = r := pow_one r
  nlinarith [sq_nonneg (ptn_coeff p f S), hrpow, hr0.le]


theorem esa_logBalance_threshold {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    0 < Real.exp (-(1 / (2 * (p * (1 - p))))) ∧
    Real.exp (-(1 / (2 * (p * (1 - p))))) < 1 ∧
    4 * (p * (1 - p)) * Real.log (1 / Real.exp (-(1 / (2 * (p * (1 - p)))))) = 2 := by
  have hσ2pos : 0 < p * (1 - p) := by nlinarith
  refine ⟨Real.exp_pos _, ?_, ?_⟩
  · rw [Real.exp_lt_one_iff]
    have : 0 < 1 / (2 * (p * (1 - p))) := by positivity
    linarith
  · rw [one_div, Real.log_inv, Real.log_exp, neg_neg, one_div]
    have hne : (2 : ℝ) * (p * (1 - p)) ≠ 0 := by positivity
    rw [show (4 : ℝ) * (p * (1 - p)) = 2 * (2 * (p * (1 - p))) from by ring]
    rw [mul_assoc, mul_inv_cancel₀ hne, mul_one]


theorem esa_maxInfl_pos_of_var_pos {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    {ν : E → Bool → ℝ} (hν : OSSS.IsProbWeight ν) (φ : ConfigSpace E → Bool)
    (hVar : 0 < OSSS.var ν (fun ω => if φ ω then (1 : ℝ) else 0)) :
    0 < maxInfl ν (fun ω => if φ ω then (1 : ℝ) else 0) := by
  set f := fun ω => if φ ω then (1 : ℝ) else 0 with hf
  have hVT : OSSS.var ν f ≤ totalInfl ν f := kkl_var_le_total_influence hν φ
  have hTm : totalInfl ν f ≤ (Fintype.card E : ℝ) * maxInfl ν f := kkl_maxInfl_ge_avg ν f
  have hcard : (0 : ℝ) < (Fintype.card E : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hmnn : 0 ≤ maxInfl ν f := kkl_maxInfl_nonneg hν f
  
  by_contra hle
  rw [not_lt] at hle
  have : maxInfl ν f = 0 := le_antisymm hle hmnn
  rw [this, mul_zero] at hTm
  linarith [hVT, hTm, hVar]


end StatMech.Probability
