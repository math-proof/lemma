/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/SpliceST1.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.TailSelMPClose.Part2
import Def.StatisticalMechanics.Code.OSSS.SpliceST1.Part2
open scoped BigOperators ENNReal
open Finset MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000


namespace StatMech

namespace OSSS

namespace AdaptDisintegration

open OSSS.Monotonic OSSS.Coding OSSS.GrandCoupling OSSS.GrandCouplingAssembly

open StatMech.Probability OSSS.AdaptiveTau OSSS.AdaptMConditional

variable {E : Type*} [Fintype E] [DecidableEq E]


lemma sp1_headExtC_meas {n : ℕ} (t : ℕ) (htn : t < n) (A : {i : Fin n // (i:ℕ) < t} → ℝ) :
    Measurable (fun c : sp1_Sing n t → ℝ => sp1_headExtC t htn A c) := by
  refine measurable_pi_lambda (fun (c : sp1_Sing n t → ℝ) => sp1_headExtC t htn A c)
    (fun i => ?_)
  unfold sp1_headExtC
  by_cases h : (i:ℕ) < t
  · simp only [h, dif_pos]; exact measurable_const
  · simp only [h, dif_neg, not_false_iff]; exact measurable_pi_apply _


lemma sp1_acp_join_compat {n : ℕ} (t : ℕ) (htn : t < n) (A : {i : Fin n // (i:ℕ) < t} → ℝ)
    (B : {i : Fin n // ¬ (i:ℕ) < t} → ℝ) :
    acp_join t A B
      = acp_join (t+1) (sp1_headExtC t htn A ((sp1_tailDisint n t B).2))
          ((sp1_tailDisint n t B).1) := by
  have h2 : (sp1_tailDisint n t B).2 ⟨⟨⟨t, htn⟩, by simp⟩, by simp⟩ = B ⟨⟨t, htn⟩, by simp⟩ := by
    unfold sp1_tailDisint
    show ((MeasurableEquiv.prodCongr (sp1_renTail n t) (MeasurableEquiv.refl (sp1_Sing n t → ℝ)))
      ((MeasurableEquiv.piEquivPiSubtypeProd _ _) B)).2 _ = _
    rfl
  funext i
  by_cases hit : (i:ℕ) < t
  · rw [tsc_acp_join_head t A B i hit, tsc_acp_join_head (t+1) _ _ i (by omega)]
    unfold sp1_headExtC; simp [hit]
  · by_cases hit1 : (i:ℕ) < t+1
    · have hieq : (i:ℕ) = t := by omega
      rw [tsc_acp_join_tail t A B i hit, tsc_acp_join_head (t+1) _ _ i hit1]
      unfold sp1_headExtC; simp only [hit, dif_neg, not_false_iff]
      rw [h2]; congr 1; apply Subtype.ext; apply Fin.ext; exact hieq
    · rw [tsc_acp_join_tail t A B i hit, tsc_acp_join_tail (t+1) _ _ i hit1]
      show B _ = (sp1_tailDisint n t B).1 _
      unfold sp1_tailDisint sp1_renTail; rfl


end AdaptDisintegration
end OSSS
end StatMech
