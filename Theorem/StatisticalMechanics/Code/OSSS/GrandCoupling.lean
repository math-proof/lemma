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
import Instance.StatisticalMechanics.Code.OSSS.GrandCoupling
open scoped BigOperators ENNReal
open Finset MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace OSSS

namespace GrandCoupling

open OSSS.Monotonic OSSS.Coding StatMech.Probability

variable {E : Type*} [Fintype E] [DecidableEq E]


lemma condProbBit_true_eq_open (μ : ConfigSpace E → ℝ) (F : Finset E) (η : ConfigSpace E)
    (e : E) :
    condProbBit μ F η e true = condProbOpen μ F η e := by
  unfold condProbBit condProbOpen condMass OpenAt
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hag : Agree F η ω
  · by_cases hb : ω e = true
    · rw [if_pos ⟨hag, hb⟩, if_pos hag, Set.indicator_of_mem (by exact hb)]; ring
    · rw [if_neg (by tauto)]; rw [Set.indicator_of_notMem (by simp [hb])]; ring
  · rw [if_neg (by tauto), if_neg hag]
    by_cases hb : ω e = true
    · rw [Set.indicator_of_mem (show ω ∈ {ω | ω e = true} from hb)]; ring
    · rw [Set.indicator_of_notMem (by simp [hb])]; ring


lemma condProbClosed_eq_one_sub_open (μ : ConfigSpace E → ℝ) (F : Finset E)
    (η : ConfigSpace E) (e : E) (hF : 0 < condNorm μ F η) :
    condProbClosed μ F η e = 1 - condProbOpen μ F η e := by
  have h := condProbBit_true_add_false μ F η e hF.ne'
  rw [condProbBit_true_eq_open] at h
  unfold condProbClosed
  linarith


lemma condProbClosed_antitone {μ : ConfigSpace E → ℝ} (hmono : IsMonotonicMeasure μ)
    (F : Finset E) (e : E) (ξ ζ : ConfigSpace E) (hle : ∀ f ∈ F, ξ f ≤ ζ f)
    (hZξ : 0 < condNorm μ F ξ) (hZζ : 0 < condNorm μ F ζ) :
    condProbClosed μ F ζ e ≤ condProbClosed μ F ξ e := by
  rw [condProbClosed_eq_one_sub_open μ F ξ e hZξ,
      condProbClosed_eq_one_sub_open μ F ζ e hZζ]
  have := hmono e F ξ ζ hle hZξ hZζ
  linarith


lemma decide_ge_mono {a a' thr thr' : ℝ} (ha : a ≤ a') (hthr : thr' ≤ thr) :
    decide (a ≥ thr) ≤ decide (a' ≥ thr') := by
  by_cases h : a ≥ thr
  · have h' : a' ≥ thr' := le_trans hthr (le_trans h ha)
    rw [decide_eq_true h, decide_eq_true h']
  · rw [decide_eq_false h]; exact bot_le


lemma codePrefix_mono_u {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n → E)
    (u u' : Fin n → ℝ) (hle : u ≤ u') (k : ℕ) :
    codePrefix μ σ u k ≤ codePrefix μ σ u' k := by
  induction k with
  | zero => intro e; simp [codePrefix]
  | succ k ih =>
    by_cases hk : k < n
    · intro e
      conv_lhs => unfold codePrefix
      conv_rhs => unfold codePrefix
      simp only [hk, dif_pos]
      by_cases hek : e = σ ⟨k, hk⟩
      · subst hek
        rw [Function.update_self, Function.update_self]
        have hthr : condProbClosed μ (prefixSet σ k) (codePrefix μ σ u' k) (σ ⟨k, hk⟩)
            ≤ condProbClosed μ (prefixSet σ k) (codePrefix μ σ u k) (σ ⟨k, hk⟩) :=
          condProbClosed_antitone hmono (prefixSet σ k) (σ ⟨k, hk⟩)
            (codePrefix μ σ u k) (codePrefix μ σ u' k) (fun f _ => ih f)
            (condNorm_pos hpos _ _) (condNorm_pos hpos _ _)
        exact decide_ge_mono (hle ⟨k, hk⟩) hthr
      · rw [Function.update_of_ne hek, Function.update_of_ne hek]; exact ih e
    · intro e
      conv_lhs => unfold codePrefix
      conv_rhs => unfold codePrefix
      simp only [hk, dif_neg, not_false_iff]; exact ih e


lemma codeMap_mono_u {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n → E) :
    Monotone (fun u : Fin n → ℝ => codeMap μ σ u) :=
  fun u u' hle => codePrefix_mono_u hpos hmono σ u u' hle n


lemma measurable_codeMap (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E) :
    Measurable (fun u : Fin n → ℝ => codeMap μ (σ : Fin n → E) u) := by
  apply measurable_to_countable'
  intro x
  show MeasurableSet {u : Fin n → ℝ | codeMap μ (σ : Fin n → E) u = x}
  have hrw : {u : Fin n → ℝ | codeMap μ (σ : Fin n → E) u = x}
      = ⋂ t : Fin n, {u : Fin n → ℝ |
          x ((σ : Fin n → E) t) = decide (u t ≥ thr μ (σ : Fin n → E) x t)} := by
    ext u; simp only [Set.mem_setOf_eq, Set.mem_iInter]; exact codeMap_eq_iff μ σ x u
  rw [hrw]
  apply MeasurableSet.iInter
  intro t
  by_cases hbit : x ((σ : Fin n → E) t)
  · have hset : {u : Fin n → ℝ | x ((σ : Fin n → E) t) = decide (u t ≥ thr μ (σ : Fin n → E) x t)}
        = {u : Fin n → ℝ | u t ≥ thr μ (σ : Fin n → E) x t} := by
      ext u; simp only [Set.mem_setOf_eq, hbit]
      constructor
      · intro h; have := h.symm; rw [decide_eq_true_eq] at this; exact this
      · intro h; symm; rw [decide_eq_true_eq]; exact h
    rw [hset]; exact measurableSet_le measurable_const (measurable_pi_apply t)
  · have hbit' : x ((σ : Fin n → E) t) = false := by
      cases h : x ((σ : Fin n → E) t); rfl; exact absurd h hbit
    have hset : {u : Fin n → ℝ | x ((σ : Fin n → E) t) = decide (u t ≥ thr μ (σ : Fin n → E) x t)}
        = {u : Fin n → ℝ | u t < thr μ (σ : Fin n → E) x t} := by
      ext u; simp only [Set.mem_setOf_eq, hbit']
      constructor
      · intro h; rw [eq_comm, decide_eq_false_iff_not, not_le] at h; exact h
      · intro h; symm; rw [decide_eq_false_iff_not, not_le]; exact h
    rw [hset]; exact measurableSet_lt (measurable_pi_apply t) measurable_const


lemma measurable_g_codeMap (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (g : ConfigSpace E → ℝ) :
    Measurable (fun u : Fin n → ℝ => g (codeMap μ (σ : Fin n → E) u)) :=
  (measurable_of_finite g).comp (measurable_codeMap μ σ)


end GrandCoupling
end OSSS
end StatMech
