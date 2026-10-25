/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Coding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.Monotonic.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.OSSS.Part6
import Def.StatisticalMechanics.Code.OSSS.Coding.Part5
open scoped BigOperators
open Finset MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace OSSS.Coding

open OSSS.Monotonic

variable {E : Type*} [Fintype E] [DecidableEq E]


lemma codeFibre_eq_box (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    {n : ℕ} (σ : Fin n ≃ E) (x : ConfigSpace E) :
    codeFibre μ σ x = Set.univ.pi (codeInterval μ (σ : Fin n → E) x) := by
  ext u
  simp only [codeFibre, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
  constructor
  · rintro ⟨hcube, hx⟩ t
    have hb := (codeMap_eq_iff μ σ x u).mp hx t
    have h0 : 0 ≤ u t := (hcube t).1
    have h1 : u t < 1 := (hcube t).2
    unfold codeInterval
    by_cases hbit : x ((σ : Fin n → E) t)
    · simp only [hbit, if_true]
      rw [hbit] at hb
      have hd : decide (u t ≥ thr μ (σ : Fin n → E) x t) = true := hb.symm
      rw [decide_eq_true_eq] at hd
      exact ⟨hd, h1⟩
    · simp only [hbit, Bool.false_eq_true, if_false]
      rw [Bool.not_eq_true] at hbit
      rw [hbit] at hb
      have hd : decide (u t ≥ thr μ (σ : Fin n → E) x t) = false := hb.symm
      rw [decide_eq_false_iff_not, not_le] at hd
      exact ⟨h0, hd⟩
  · intro hmem
    have hthr := fun t => thr_mem_Icc μ hpos (σ : Fin n → E) x t
    refine ⟨fun t => ?_, ?_⟩
    · have hm := hmem t
      unfold codeInterval at hm
      obtain ⟨h0, h1⟩ := hthr t
      by_cases hbit : x ((σ : Fin n → E) t)
      · simp only [hbit, if_true] at hm
        exact ⟨le_trans h0 hm.1, hm.2⟩
      · simp only [hbit, Bool.false_eq_true, if_false] at hm
        exact ⟨hm.1, lt_of_lt_of_le hm.2 h1⟩
    · rw [codeMap_eq_iff μ σ x u]
      intro t
      have hm := hmem t
      unfold codeInterval at hm
      by_cases hbit : x ((σ : Fin n → E) t)
      · simp only [hbit, if_true] at hm
        rw [hbit]; symm; rw [decide_eq_true_eq]; exact hm.1
      · simp only [hbit, Bool.false_eq_true, if_false] at hm
        rw [Bool.not_eq_true] at hbit
        rw [hbit]; symm; rw [decide_eq_false_iff_not, not_le]; exact hm.2


lemma volume_codeInterval (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    {n : ℕ} (σ : Fin n → E) (x : ConfigSpace E) (t : Fin n) :
    (volume (codeInterval μ σ x t)).toReal
      = condProbBit μ (prefixSet σ (t : ℕ)) x (σ t) (x (σ t)) := by
  have hZ : 0 < condNorm μ (prefixSet σ (t : ℕ)) x := OSSS.Monotonic.condNorm_pos hpos _ _
  have hsum := condProbBit_true_add_false μ (prefixSet σ (t : ℕ)) x (σ t) hZ.ne'
  obtain ⟨h0, h1⟩ := thr_mem_Icc μ hpos σ x t
  have hthr_eq : thr μ σ x t = condProbBit μ (prefixSet σ (t : ℕ)) x (σ t) false := rfl
  unfold codeInterval
  by_cases hbit : x (σ t)
  · simp only [hbit, if_true, Real.volume_Ico]
    rw [ENNReal.toReal_ofReal (by linarith)]
    rw [hthr_eq] at *
    linarith
  · simp only [hbit, Bool.false_eq_true, if_false, Real.volume_Ico, sub_zero]
    rw [ENNReal.toReal_ofReal h0, hthr_eq]


theorem codeProb_eq_mass (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (x : ConfigSpace E) :
    (∏ t : Fin n, condProbBit μ (prefixSet (σ : Fin n → E) (t : ℕ)) x
        ((σ : Fin n → E) t) (x ((σ : Fin n → E) t)))
      = μ x := by
  have htel := condNorm_prefix_telescope μ hpos (σ : Fin n → E) x n
  rw [prefixSet_card σ, condNorm_univ, prefixIdx_self, condNorm_empty, hμ1, mul_one] at htel
  rw [← htel]


theorem volume_codeFibre (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (x : ConfigSpace E) :
    (volume (codeFibre μ σ x)).toReal = μ x := by
  rw [codeFibre_eq_box μ hpos σ x, volume_pi_pi, ENNReal.toReal_prod]
  rw [← codeProb_eq_mass μ hpos hμ1 σ x]
  apply Finset.prod_congr rfl
  intro t _
  exact volume_codeInterval μ hpos (σ : Fin n → E) x t


open OSSS.DecisionTree

omit [Fintype E] in


lemma eval_eq_of_agree_on_queried (T : DecisionTree E) (ω ω' : ConfigSpace E)
    (h : ∀ e ∈ T.queried ω, ω' e = ω e) : T.eval ω' = T.eval ω := by
  induction T with
  | leaf b => rfl
  | node e t f IHt IHf =>
    have hmem : e ∈ (DecisionTree.node e t f).queried ω := by
      unfold DecisionTree.queried; exact Finset.mem_insert_self e _
    have he : ω' e = ω e := h e hmem
    unfold DecisionTree.eval
    rw [he]
    by_cases hb : ω e
    · simp only [hb, if_true]
      refine IHt ?_
      intro i hi
      apply h i
      unfold DecisionTree.queried
      rw [hb]
      exact Finset.mem_insert_of_mem (by simp only [if_true]; exact hi)
    · simp only [hb, Bool.false_eq_true, if_false]
      refine IHf ?_
      intro i hi
      apply h i
      unfold DecisionTree.queried
      simp only [hb, Bool.false_eq_true, if_false]
      exact Finset.mem_insert_of_mem hi


end OSSS.Coding
end StatMech
