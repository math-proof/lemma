/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/ReachBoxCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.RevealmentBoxCrossing.Part3
import Theorem.StatisticalMechanics.Code.OSSS.RevealmentCrossBox.Part7
open scoped BigOperators
open MeasureTheory

set_option linter.unusedSectionVars false


namespace StatMech

namespace OSSS

namespace ReachBoxCrossing

open OSSS.Monotonic OSSS.AdaptMConditional StatMech.Probability

open StatMech.OSSS.MonotonicFK

open StatMech.OSSS.AdaptDisintegration

open OSSS.GrandCoupling OSSS.Coding

open StatMech.OSSS.RevealmentBoundAssembly

open StatMech.OSSS.RevealmentBoxCrossing

open StatMech.OSSS.RevealmentConstruction

open StatMech.Lattice

variable {E : Type*} [Fintype E] [DecidableEq E]


theorem mean_indicator_le {μ : ConfigSpace E → ℝ} (hμ0 : ∀ ω, 0 ≤ μ ω)
    (g : ConfigSpace E → ℝ) (P : ConfigSpace E → Prop) [DecidablePred P]
    (hg : ∀ X, g X ≤ if P X then (1 : ℝ) else 0) :
    Lindeberg.mean μ g
      ≤ Lindeberg.mean μ (fun X => if P X then (1 : ℝ) else 0) := by
  unfold Lindeberg.mean
  apply Finset.sum_le_sum
  intro X _
  exact mul_le_mul_of_nonneg_right (hg X) (hμ0 X)


theorem reachProb_le_of_undet_imp {μ : ConfigSpace E → ℝ} (hμ0 : ∀ ω, 0 ≤ μ ω)
    {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) (e : E)
    (P : ConfigSpace E → Prop) [DecidablePred P]
    (h : ∀ X, ¬ detAtC (σ : Fin n → E) f X (σ.symm e : ℕ) → P X) :
    reachProb μ σ f e ≤ Lindeberg.mean μ (fun X => if P X then (1 : ℝ) else 0) := by
  unfold reachProb
  apply mean_indicator_le hμ0
  intro X
  unfold reachInd
  by_cases hdet : detAtC (σ : Fin n → E) f X (σ.symm e : ℕ)
  · rw [if_pos hdet]; split <;> norm_num
  · rw [if_neg hdet, if_pos (h X hdet)]


theorem mean_indicator_or_le {μ : ConfigSpace E → ℝ} (hμ0 : ∀ ω, 0 ≤ μ ω)
    (P Q : ConfigSpace E → Prop) [DecidablePred P] [DecidablePred Q] :
    Lindeberg.mean μ (fun X => if P X ∨ Q X then (1 : ℝ) else 0)
      ≤ Lindeberg.mean μ (fun X => if P X then (1 : ℝ) else 0)
        + Lindeberg.mean μ (fun X => if Q X then (1 : ℝ) else 0) := by
  unfold Lindeberg.mean
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro X _
  simp only []
  have hPnonNeg : (0 : ℝ) ≤ if P X then (1 : ℝ) else 0 := by split <;> norm_num
  have hQnonNeg : (0 : ℝ) ≤ if Q X then (1 : ℝ) else 0 := by split <;> norm_num
  rw [← add_mul]
  apply mul_le_mul_of_nonneg_right _ (hμ0 X)
  by_cases hPQ : P X ∨ Q X
  · rw [if_pos hPQ]
    rcases hPQ with hP | hQ
    · rw [if_pos hP]; linarith
    · rw [if_pos hQ]; linarith
  · rw [if_neg hPQ]; linarith


theorem reachProb_le_of_undet_imp_or {μ : ConfigSpace E → ℝ} (hμ0 : ∀ ω, 0 ≤ μ ω)
    {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) (e : E)
    (P Q : ConfigSpace E → Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀ X, ¬ detAtC (σ : Fin n → E) f X (σ.symm e : ℕ) → P X ∨ Q X) :
    reachProb μ σ f e
      ≤ Lindeberg.mean μ (fun X => if P X then (1 : ℝ) else 0)
        + Lindeberg.mean μ (fun X => if Q X then (1 : ℝ) else 0) :=
  (reachProb_le_of_undet_imp hμ0 σ f e (fun X => P X ∨ Q X) h).trans
    (mean_indicator_or_le hμ0 P Q)


end ReachBoxCrossing
end OSSS
end StatMech
