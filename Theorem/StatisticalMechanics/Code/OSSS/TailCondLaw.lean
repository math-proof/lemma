/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailCondLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.AdaptCondReduction
open scoped BigOperators ENNReal
open Finset MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace OSSS

namespace AdaptDisintegration

open OSSS.Monotonic OSSS.Coding OSSS.GrandCoupling OSSS.GrandCouplingAssembly

open StatMech.Probability OSSS.AdaptiveTau OSSS.AdaptMConditional

variable {E : Type*} [Fintype E] [DecidableEq E]


lemma atc_adaptWt_join_indep_head {n : ℕ} (t s m : ℕ) (hst : t ≤ s)
    (A A' : {i : Fin n // (i : ℕ) < t} → ℝ) (B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ)
    (V : Fin n → ℝ) :
    adaptWt (acp_join t A B) V m s = adaptWt (acp_join t A' B) V m s := by
  funext i
  unfold adaptWt
  by_cases h1 : (i : ℕ) < s
  · simp [h1]
  · simp only [h1, if_false]
    by_cases h2 : (i : ℕ) < m
    · simp only [h2, if_true]
      have hit : ¬ (i : ℕ) < t := by omega
      show acp_join t A B i = acp_join t A' B i
      have e1 : acp_join t A B i = if h : (i : ℕ) < t then A ⟨i, h⟩ else B ⟨i, h⟩ := rfl
      have e2 : acp_join t A' B i = if h : (i : ℕ) < t then A' ⟨i, h⟩ else B ⟨i, h⟩ := rfl
      rw [e1, e2, dif_neg hit, dif_neg hit]
    · simp [h2]


end AdaptDisintegration
end OSSS
end StatMech
