/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Coding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.Monotonic.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.OSSS.Part6
import Def.StatisticalMechanics.Code.OSSS.Coding.Part3
open scoped BigOperators
open Finset MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace OSSS.Coding

open OSSS.Monotonic

variable {E : Type*} [Fintype E] [DecidableEq E]


lemma codePrefix_succ_self (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n → E)
    (u : Fin n → ℝ) (t : ℕ) (ht : t < n) :
    codePrefix μ σ u (t+1) (σ ⟨t, ht⟩)
      = decide (u ⟨t, ht⟩ ≥ condProbClosed μ (prefixSet σ t) (codePrefix μ σ u t) (σ ⟨t, ht⟩)) := by
  conv_lhs => unfold codePrefix
  simp only [ht, dif_pos, Function.update_self]


lemma codePrefix_stable (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n → E)
    (hσ : Function.Injective σ) (u : Fin n → ℝ) (k m : ℕ) (hkm : k ≤ m) (e : E)
    (he : e ∈ prefixSet σ k) :
    codePrefix μ σ u m e = codePrefix μ σ u k e := by
  obtain ⟨s, hs, rfl⟩ := (mem_prefixSet_iff σ k _).mp he
  induction m with
  | zero => omega
  | succ m ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hkm) with hlt | heq
    · have hkm' : k ≤ m := by omega
      conv_lhs => unfold codePrefix
      by_cases hmn : m < n
      · simp only [hmn, dif_pos]
        have hne : σ s ≠ σ ⟨m, hmn⟩ := by
          intro h; have := hσ h; rw [this] at hs; simp at hs; omega
        rw [Function.update_of_ne hne]; exact ih hkm'
      · simp only [hmn, dif_neg, not_false_iff]; exact ih hkm'
    · rw [heq]


lemma codePrefix_agree_codeMap (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n → E)
    (hσ : Function.Injective σ) (u : Fin n → ℝ) (m : ℕ) (hm : m ≤ n) :
    ∀ e ∈ prefixSet σ m, codePrefix μ σ u m e = codeMap μ σ u e := by
  intro e he
  unfold codeMap
  exact (codePrefix_stable μ σ hσ u m n hm e he).symm


end OSSS.Coding
end StatMech
