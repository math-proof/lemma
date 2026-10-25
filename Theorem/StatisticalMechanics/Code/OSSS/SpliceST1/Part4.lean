/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/SpliceST1.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.TailSelMPClose.Part2
import Def.StatisticalMechanics.Code.OSSS.SpliceST1.Part3
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


theorem sp1_reshuf_mp {n : ℕ} (t : ℕ) :
    MeasurePreserving (sp1_reshuf (n := n) t) ((ubfTail n t).prod (Vcube n))
      ((Measure.pi (fun _ : sp1_Sing n t => unitMeasure)).prod
        ((ubfTail n (t+1)).prod (Vcube n))) := by
  set κ := Measure.pi (fun _ : sp1_Sing n t => unitMeasure) with hκ
  
  have hstep1 : MeasurePreserving (Prod.map (sp1_tailDisint n t) (id : (Fin n → ℝ) → _))
      ((ubfTail n t).prod (Vcube n)) (((ubfTail n (t+1)).prod κ).prod (Vcube n)) :=
    (sp1_tailSplit_mp n t).prod (MeasurePreserving.id (Vcube n))
  
  have hswap : MeasurePreserving
      (Prod.swap : (({i : Fin n // ¬ (i:ℕ) < t+1} → ℝ) × (sp1_Sing n t → ℝ)) → _)
      ((ubfTail n (t+1)).prod κ) (κ.prod (ubfTail n (t+1))) :=
    Measure.measurePreserving_swap
  have hstep2 : MeasurePreserving
      (Prod.map (Prod.swap : (({i : Fin n // ¬ (i:ℕ) < t+1} → ℝ) × (sp1_Sing n t → ℝ)) → _)
        (id : (Fin n → ℝ) → _))
      (((ubfTail n (t+1)).prod κ).prod (Vcube n)) ((κ.prod (ubfTail n (t+1))).prod (Vcube n)) :=
    hswap.prod (MeasurePreserving.id (Vcube n))
  
  have hstep3 : MeasurePreserving
      (MeasurableEquiv.prodAssoc :
        ((sp1_Sing n t → ℝ) × ({i : Fin n // ¬ (i:ℕ) < t+1} → ℝ)) × (Fin n → ℝ) ≃ᵐ _)
      ((κ.prod (ubfTail n (t+1))).prod (Vcube n)) (κ.prod ((ubfTail n (t+1)).prod (Vcube n))) :=
    measurePreserving_prodAssoc κ (ubfTail n (t+1)) (Vcube n)
  have hcomp := (hstep3.comp hstep2).comp hstep1
  
  have heq : ((⇑MeasurableEquiv.prodAssoc) ∘
      (Prod.map (Prod.swap : (({i : Fin n // ¬ (i:ℕ) < t+1} → ℝ) × (sp1_Sing n t → ℝ)) → _)
        (id : (Fin n → ℝ) → _))) ∘
      (Prod.map (sp1_tailDisint n t) (id : (Fin n → ℝ) → _)) = sp1_reshuf (n := n) t := by
    funext p; rfl
  rw [heq] at hcomp
  exact hcomp


lemma sp1_reshuf_meas {n : ℕ} (t : ℕ) : Measurable (sp1_reshuf (n := n) t) :=
  (sp1_reshuf_mp t).measurable


theorem sp1_selRand_factor (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (t : ℕ) (htn : t < n) (A : {i : Fin n // (i:ℕ) < t} → ℝ) :
    atl_selRand μ σ f t (t+1) A
      = (Function.uncurry (sp1_G μ σ f t htn A)) ∘ (sp1_reshuf (n := n) t) := by
  funext p
  obtain ⟨B, V⟩ := p
  show adaptWt (acp_join t A B) V (stopVal μ σ f (acp_join t A B)) (t+1)
      = adaptWt (acp_join (t+1) (sp1_headExtC t htn A ((sp1_tailDisint n t B).2)) ((sp1_tailDisint n t B).1)) V
          (stopVal μ σ f (acp_join (t+1) (sp1_headExtC t htn A ((sp1_tailDisint n t B).2)) ((sp1_tailDisint n t B).1))) (t+1)
  rw [sp1_acp_join_compat t htn A B]


lemma sp1_G_uncurry_meas (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ)
    (t : ℕ) (htn : t < n) (A : {i : Fin n // (i:ℕ) < t} → ℝ) :
    Measurable (Function.uncurry (sp1_G μ σ f t htn A)) := by
  
  
  set Hd : (sp1_Sing n t → ℝ) × (({i : Fin n // ¬ (i:ℕ) < t+1} → ℝ) × (Fin n → ℝ)) → (Fin n → ℝ) :=
    fun q => acp_join (t+1) (sp1_headExtC t htn A q.1) q.2.1 with hHd
  have hHdm : Measurable Hd := by
    show Measurable (fun q : (sp1_Sing n t → ℝ) × (({i : Fin n // ¬ (i:ℕ) < t+1} → ℝ) × (Fin n → ℝ)) =>
      (ubfSplit n (t+1)).symm (sp1_headExtC t htn A q.1, q.2.1))
    exact (ubfSplit n (t+1)).symm.measurable.comp
      (((sp1_headExtC_meas t htn A).comp measurable_fst).prodMk
        (measurable_fst.comp measurable_snd))
  
  have hstop : Measurable (fun q => stopVal μ σ f (Hd q)) :=
    (measurable_stopVal μ σ f).comp hHdm
  
  have hV : Measurable (fun q : (sp1_Sing n t → ℝ) × (({i : Fin n // ¬ (i:ℕ) < t+1} → ℝ) × (Fin n → ℝ)) =>
      q.2.2) := measurable_snd.comp measurable_snd
  
  have key : ∀ m : ℕ, Measurable (fun q : (sp1_Sing n t → ℝ) × (({i : Fin n // ¬ (i:ℕ) < t+1} → ℝ) × (Fin n → ℝ)) =>
      adaptWt (Hd q) (q.2.2) m (t+1)) :=
    fun m => (measurable_adaptWt_fixed m (t+1)).comp (hHdm.prodMk hV)
  have hglue : Measurable (fun mq : ℕ × ((sp1_Sing n t → ℝ) × (({i : Fin n // ¬ (i:ℕ) < t+1} → ℝ) × (Fin n → ℝ))) =>
      adaptWt (Hd mq.2) (mq.2.2.2) mq.1 (t+1)) :=
    measurable_from_prod_countable_right key
  exact hglue.comp (hstop.prodMk measurable_id)


theorem sp1_tailSelMP (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ)
    (t : ℕ) (htn : t < n) (A : {i : Fin n // (i:ℕ) < t} → ℝ) :
    atl_TailSelMP μ σ f t (t+1) A := by
  show MeasurePreserving (atl_selRand μ σ f t (t+1) A) ((ubfTail n t).prod (Vcube n)) (Vcube n)
  refine ⟨tsm_measurable_selRand μ σ f t (t+1) A, ?_⟩
  rw [sp1_selRand_factor μ σ f t htn A,
    ← Measure.map_map (sp1_G_uncurry_meas μ σ f t htn A) (sp1_reshuf_meas t),
    (sp1_reshuf_mp t).map_eq]
  
  
  exact sp1_map_uncurry_const _ _ (sp1_G_uncurry_meas μ σ f t htn A)
    (fun c => (tsc_tailSelMP_at_s_eq_t μ σ f (t+1) (sp1_headExtC t htn A c)).map_eq)


theorem sp1_restrictedSum_of_tailSelMP (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (t s : ℕ) (A : {i : Fin n // (i:ℕ) < t} → ℝ)
    (hMP : atl_TailSelMP μ σ f t s A) :
    tsm_TailSelMP_restrictedSum μ σ f t s A := by
  show (Measure.sum (fun k => Measure.map (osp_tailSelFixed t s k A)
      (((ubfTail n t).prod (Vcube n)).restrict (tsm_switchPiece μ σ f t A k)))) = Vcube n
  
  have hpiece : ∀ k, Measure.map (osp_tailSelFixed t s k A)
        (((ubfTail n t).prod (Vcube n)).restrict (tsm_switchPiece μ σ f t A k))
      = Measure.map (atl_selRand μ σ f t s A)
        (((ubfTail n t).prod (Vcube n)).restrict (tsm_switchPiece μ σ f t A k)) := by
    intro k
    refine tsm_map_restrict_congr ((ubfTail n t).prod (Vcube n)) (tsm_switchPiece μ σ f t A k)
      (osp_tailSelFixed_meas t s k A) (tsm_measurable_selRand μ σ f t s A) ?_
    intro p hp
    exact (tsm_selRand_eq_on_piece μ σ f t s A k p hp).symm
  simp_rw [hpiece]
  rw [← Measure.map_sum (tsm_measurable_selRand μ σ f t s A).aemeasurable,
    ← Measure.restrict_iUnion (tsm_switchPiece_disj μ σ f t A) (tsm_switchPiece_meas μ σ f t A),
    tsm_switchPiece_cover μ σ f t A, Measure.restrict_univ]
  exact hMP.map_eq


theorem sp1_restrictedSum_at_s_eq_t_succ (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (t : ℕ) (htn : t < n) (A : {i : Fin n // (i:ℕ) < t} → ℝ) :
    tsm_TailSelMP_restrictedSum μ σ f t (t+1) A :=
  sp1_restrictedSum_of_tailSelMP μ σ f t (t+1) A (sp1_tailSelMP μ σ f t htn A)

end AdaptDisintegration
end OSSS
end StatMech
