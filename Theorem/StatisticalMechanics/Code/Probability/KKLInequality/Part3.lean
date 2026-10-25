/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLInequality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.OSSS.Part6
import Theorem.StatisticalMechanics.Code.OSSS.Poincare.Part2
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Def.StatisticalMechanics.Code.Probability.KKLInequality.Part2
open scoped BigOperators
open Finset


namespace StatMech

namespace Probability

open StatMech.OSSS

variable {E : Type*} [Fintype E] [DecidableEq E]


theorem kkl_infl_le_maxInfl [Nonempty E] (ν : E → Bool → ℝ) (g : ConfigSpace E → ℝ)
    (e : E) : OSSS.infl ν g e ≤ maxInfl ν g :=
  Finset.le_sup' _ (Finset.mem_univ e)


theorem kkl_exists_maxInfl [Nonempty E] (ν : E → Bool → ℝ) (g : ConfigSpace E → ℝ) :
    ∃ e, OSSS.infl ν g e = maxInfl ν g := by
  unfold maxInfl
  obtain ⟨e, _, he⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := E)) (OSSS.infl ν g)
  exact ⟨e, he.symm⟩


theorem kkl_maxInfl_nonneg [Nonempty E] {ν : E → Bool → ℝ} (hν : IsProbWeight ν)
    (g : ConfigSpace E → ℝ) : 0 ≤ maxInfl ν g := by
  obtain ⟨e, he⟩ := kkl_exists_maxInfl ν g
  rw [← he]; exact kkl_infl_nonneg hν g e


theorem kkl_maxInfl_ge_avg [Nonempty E] (ν : E → Bool → ℝ) (g : ConfigSpace E → ℝ) :
    totalInfl ν g ≤ (Fintype.card E : ℝ) * maxInfl ν g := by
  unfold totalInfl
  calc ∑ e, OSSS.infl ν g e
      ≤ ∑ _e : E, maxInfl ν g := by
        apply Finset.sum_le_sum; intro e _; exact kkl_infl_le_maxInfl ν g e
    _ = (Fintype.card E : ℝ) * maxInfl ν g := by
        rw [Finset.sum_const, Finset.card_univ]; ring


theorem kkl_var_nonneg {ν : E → Bool → ℝ} (hν : IsProbWeight ν) (g : ConfigSpace E → ℝ) :
    0 ≤ OSSS.var ν g := by
  have hkey : OSSS.var ν g = OSSS.expect ν (fun ω => (g ω - OSSS.expect ν g) ^ 2) := by
    unfold OSSS.var OSSS.cov OSSS.expect
    have hsum1 : (∑ ω, OSSS.weight ν ω) = 1 := by
      have := OSSS.expect_one hν
      unfold OSSS.expect at this; simpa using this
    rw [Finset.sum_mul]
    have : ∀ ω, OSSS.weight ν ω * (g ω - (∑ ω', OSSS.weight ν ω' * g ω')) ^ 2
        = OSSS.weight ν ω * (g ω * g ω)
          - OSSS.weight ν ω * (2 * (∑ ω', OSSS.weight ν ω' * g ω')) * g ω
          + OSSS.weight ν ω * (∑ ω', OSSS.weight ν ω' * g ω') ^ 2 := by
      intro ω; ring
    simp only [this]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have e2 : (∑ ω, OSSS.weight ν ω * (2 * (∑ ω', OSSS.weight ν ω' * g ω')) * g ω)
        = 2 * (∑ ω', OSSS.weight ν ω' * g ω') * (∑ ω, OSSS.weight ν ω * g ω) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro ω _; ring
    have e3 : (∑ ω, OSSS.weight ν ω * (∑ ω', OSSS.weight ν ω' * g ω') ^ 2)
        = (∑ ω', OSSS.weight ν ω' * g ω') ^ 2 := by
      rw [← Finset.sum_mul, hsum1, one_mul]
    rw [e2, e3]
    have hgg : ∀ ω, OSSS.weight ν ω * (g ω * g ω) = OSSS.weight ν ω * g ω ^ 2 := by
      intro ω; ring
    simp only [hgg]
    rw [← Finset.sum_mul]
    set S := ∑ ω, OSSS.weight ν ω * g ω with hS
    set Q := ∑ ω, OSSS.weight ν ω * g ω ^ 2 with hQ
    ring
  rw [hkey]
  unfold OSSS.expect
  apply Finset.sum_nonneg
  intro ω _
  have hw : 0 ≤ OSSS.weight ν ω :=
    Finset.prod_nonneg (fun e _ => hν.nonneg e (ω e))
  positivity


theorem kkl_var_indicator_eq (ν : E → Bool → ℝ) (φ : ConfigSpace E → Bool) :
    OSSS.var ν (fun ω => if φ ω then (1 : ℝ) else 0)
      = OSSS.expect ν (fun ω => if φ ω then (1 : ℝ) else 0)
        * (1 - OSSS.expect ν (fun ω => if φ ω then (1 : ℝ) else 0)) := by
  set f := fun ω => if φ ω then (1 : ℝ) else 0 with hf
  unfold OSSS.var OSSS.cov
  have hsq : (fun ω => f ω * f ω) = f := by
    funext ω; simp only [hf]; by_cases h : φ ω <;> simp [h]
  rw [hsq]; ring


theorem kkl_var_le_quarter (ν : E → Bool → ℝ) (φ : ConfigSpace E → Bool) :
    OSSS.var ν (fun ω => if φ ω then (1 : ℝ) else 0) ≤ 1 / 4 := by
  rw [kkl_var_indicator_eq]
  set m := OSSS.expect ν (fun ω => if φ ω then (1 : ℝ) else 0)
  nlinarith [sq_nonneg (m - 1 / 2)]


theorem kkl_var_le_total_influence {ν : E → Bool → ℝ} (hν : IsProbWeight ν)
    (φ : ConfigSpace E → Bool) :
    OSSS.var ν (fun ω => if φ ω then (1 : ℝ) else 0)
      ≤ totalInfl ν (fun ω => if φ ω then (1 : ℝ) else 0) :=
  OSSS.Poincare.poincare hν φ


end Probability
end StatMech
