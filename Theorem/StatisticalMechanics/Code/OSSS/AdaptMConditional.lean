/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptMConditional.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveTau
import Def.StatisticalMechanics.Code.OSSS.AdaptMConditional
open scoped BigOperators ENNReal
open Finset MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace OSSS

namespace AdaptMConditional

open OSSS.Monotonic OSSS.Coding OSSS.GrandCoupling OSSS.GrandCouplingAssembly

open StatMech.Probability OSSS.LindebergTree OSSS.AdaptiveTau

variable {E : Type*} [Fintype E] [DecidableEq E]


lemma adaptWt_eq_Wt_mix {n : ℕ} (U V : Fin n → ℝ) (m t : ℕ) :
    adaptWt U V m t = Wt (mixUV U V m) V t := by
  funext i
  unfold adaptWt Wt mixUV
  by_cases ht : (i : ℕ) < t
  · simp [ht]
  · simp [ht]


lemma adaptWt_zero {n : ℕ} (U V : Fin n → ℝ) (m : ℕ) :
    adaptWt U V m 0 = mixUV U V m := by
  funext i; unfold adaptWt mixUV; simp


lemma adaptWt_card {n : ℕ} (U V : Fin n → ℝ) (m : ℕ) :
    adaptWt U V m n = V := by
  funext i; unfold adaptWt; simp [i.2]


lemma adaptWt_ge_stop {n : ℕ} (U V : Fin n → ℝ) (m t : ℕ) (htm : m ≤ t) :
    adaptWt U V m t = V := by
  funext i
  unfold adaptWt
  by_cases ht : (i : ℕ) < t
  · simp [ht]
  · have : ¬ (i : ℕ) < m := by omega
    simp [ht, this]


lemma adaptWt_agree_off {n : ℕ} (U V : Fin n → ℝ) (m t : ℕ) (ht : 1 ≤ t) :
    ∀ i : Fin n, (i : ℕ) ≠ t - 1 → adaptWt U V m t i = adaptWt U V m (t-1) i := by
  intro i hi
  unfold adaptWt
  by_cases h : (i : ℕ) < t
  · have h' : (i : ℕ) < t - 1 := by omega
    simp [h, h']
  · have h' : ¬ (i : ℕ) < t - 1 := by omega
    simp [h, h']


lemma adaptWt_at_pos {n : ℕ} (U V : Fin n → ℝ) (m t : ℕ) (ht : 1 ≤ t) (htm : t ≤ m)
    (htn : t - 1 < n) :
    adaptWt U V m t ⟨t-1, htn⟩ = V ⟨t-1, htn⟩ ∧ adaptWt U V m (t-1) ⟨t-1, htn⟩ = U ⟨t-1, htn⟩ := by
  unfold adaptWt
  refine ⟨?_, ?_⟩
  · have h : (⟨t-1, htn⟩ : Fin n).val < t := by show t - 1 < t; omega
    simp [h]
  · have h1 : ¬ (⟨t-1, htn⟩ : Fin n).val < t - 1 := by show ¬ t - 1 < t - 1; exact lt_irrefl _
    have h2 : (⟨t-1, htn⟩ : Fin n).val < m := by show t - 1 < m; omega
    simp only [h1, if_false, h2, if_true]


end AdaptMConditional
end OSSS
end StatMech
