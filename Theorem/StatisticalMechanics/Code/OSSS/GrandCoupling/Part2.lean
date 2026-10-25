/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.Coding.Part6
import Theorem.StatisticalMechanics.Code.OSSS.Lindeberg.Part4
import Theorem.StatisticalMechanics.Code.Probability.ContinuousFKG.Part3
import Def.StatisticalMechanics.Code.OSSS.GrandCoupling.Part2
open scoped BigOperators ENNReal
open Finset MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace OSSS

namespace GrandCoupling

open OSSS.Monotonic OSSS.Coding StatMech.Probability

variable {E : Type*} [Fintype E] [DecidableEq E]


lemma vcube_rawInterval (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω) {n : ℕ}
    (σ : Fin n → E) (x : ConfigSpace E) (t : Fin n) :
    (volume.restrict (Set.Icc (0:ℝ) 1) (rawInterval μ σ x t)).toReal
      = condProbBit μ (prefixSet σ (t : ℕ)) x (σ t) (x (σ t)) := by
  obtain ⟨h0, h1⟩ := thr_mem_Icc μ hpos σ x t
  have hsum := condProbBit_true_add_false μ (prefixSet σ (t : ℕ)) x (σ t)
    (OSSS.Monotonic.condNorm_pos hpos _ _).ne'
  have hthr_eq : thr μ σ x t = condProbBit μ (prefixSet σ (t : ℕ)) x (σ t) false := rfl
  unfold rawInterval
  by_cases hbit : x (σ t)
  · simp only [hbit, if_true]
    rw [Measure.restrict_apply' measurableSet_Icc]
    have hint : Set.Ici (thr μ σ x t) ∩ Set.Icc (0:ℝ) 1 = Set.Icc (thr μ σ x t) 1 := by
      ext a; simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Icc]
      constructor
      · rintro ⟨ha, _, ha1⟩; exact ⟨ha, ha1⟩
      · rintro ⟨ha, ha1⟩; exact ⟨ha, le_trans h0 ha, ha1⟩
    rw [hint, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
    rw [hthr_eq] at *; linarith
  · simp only [hbit, Bool.false_eq_true, if_false]
    rw [Measure.restrict_apply' measurableSet_Icc]
    have hint : Set.Iio (thr μ σ x t) ∩ Set.Icc (0:ℝ) 1 = Set.Ico (0:ℝ) (thr μ σ x t) := by
      ext a; simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Icc, Set.mem_Ico]
      constructor
      · rintro ⟨ha, ha0, _⟩; exact ⟨ha0, ha⟩
      · rintro ⟨ha0, ha⟩; exact ⟨ha, ha0, le_trans (le_of_lt ha) h1⟩
    rw [hint, Real.volume_Ico, sub_zero, ENNReal.toReal_ofReal h0, hthr_eq]


lemma codeMap_fibre_eq_rawbox (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (x : ConfigSpace E) :
    {u : Fin n → ℝ | codeMap μ (σ : Fin n → E) u = x}
      = Set.univ.pi (fun t => rawInterval μ (σ : Fin n → E) x t) := by
  ext u
  simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
  rw [codeMap_eq_iff μ σ x u]
  apply forall_congr'
  intro t
  unfold rawInterval
  by_cases hbit : x ((σ : Fin n → E) t)
  · simp only [hbit, if_true, Set.mem_Ici]
    constructor
    · intro h; have := h.symm; rw [decide_eq_true_eq] at this; exact this
    · intro h; symm; rw [decide_eq_true_eq]; exact h
  · simp only [hbit, Bool.false_eq_true, if_false, Set.mem_Iio]
    constructor
    · intro h; rw [eq_comm, decide_eq_false_iff_not, not_le] at h; exact h
    · intro h; symm; rw [decide_eq_false_iff_not, not_le]; exact h


lemma vcube_fibre (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    {n : ℕ} (σ : Fin n ≃ E) (x : ConfigSpace E) :
    ((Vcube n) {u | codeMap μ (σ : Fin n → E) u = x}).toReal = μ x := by
  rw [codeMap_fibre_eq_rawbox μ σ x]
  unfold Vcube
  rw [Measure.pi_pi, ENNReal.toReal_prod]
  rw [← codeProb_eq_mass μ hpos hμ1 σ x]
  apply Finset.prod_congr rfl
  intro t _
  exact vcube_rawInterval μ hpos (σ : Fin n → E) x t


theorem integral_g_codeMap (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (g : ConfigSpace E → ℝ) :
    ∫ u, g (codeMap μ (σ : Fin n → E) u) ∂(Vcube n) = ∑ x, g x * μ x := by
  have hms : ∀ x : ConfigSpace E,
      MeasurableSet {u : Fin n → ℝ | codeMap μ (σ : Fin n → E) u = x} :=
    fun x => (measurable_codeMap μ σ) (measurableSet_singleton x)
  have hpt : (fun u => g (codeMap μ (σ : Fin n → E) u))
      = (fun u => ∑ x, g x
          * (Set.indicator {u | codeMap μ (σ : Fin n → E) u = x} (fun _ => (1:ℝ)) u)) := by
    funext u
    rw [Finset.sum_eq_single (codeMap μ (σ : Fin n → E) u)]
    · rw [Set.indicator_of_mem
        (by simp : u ∈ {u' | codeMap μ (σ : Fin n → E) u' = codeMap μ (σ : Fin n → E) u})]; ring
    · intro x _ hx
      rw [Set.indicator_of_notMem
        (by simp only [Set.mem_setOf_eq]; exact fun h => hx h.symm), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hpt, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro x _
    rw [integral_const_mul, integral_indicator_const (1:ℝ) (hms x), smul_eq_mul, mul_one]
    rw [show (Vcube n).real {u | codeMap μ (σ : Fin n → E) u = x}
        = ((Vcube n) {u | codeMap μ (σ : Fin n → E) u = x}).toReal from rfl]
    rw [vcube_fibre μ hpos hμ1 σ x]
  · intro x _
    exact Integrable.const_mul (Integrable.indicator (integrable_const 1) (hms x)) _


end GrandCoupling
end OSSS
end StatMech
