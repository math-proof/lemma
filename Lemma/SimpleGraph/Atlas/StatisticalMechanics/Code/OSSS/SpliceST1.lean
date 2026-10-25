import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.OSSS.SpliceST1.Part4
open Finset MeasureTheory StatMech StatMech.OSSS StatMech.OSSS.AdaptDisintegration


/--
[sp1_map_uncurry_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/SpliceST1.lean)
-/
@[path]
private lemma sp1_map_uncurry_const_eq
  [Fintype E]
  [DecidableEq E]
  [MeasurableSpace γ]
  [MeasurableSpace α]
  [MeasurableSpace β]
  {κ : Measure γ}
  [IsProbabilityMeasure κ]
  {ν : Measure α}
  [SigmaFinite ν]
  {G : γ → α → β}
  {ξ : Measure β}
-- given
  (hG : Measurable (Function.uncurry G))
  (hcol : ∀ c, Measure.map (G c) ν = ξ) :
-- imply
  Measure.map (Function.uncurry G) (κ.prod ν) = ξ := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.sp1_map_uncurry_const κ ν hG hcol

/--
[sp1_tailSplit_mp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/SpliceST1.lean)
-/
@[path]
private lemma sp1_tailSplit_mp_eq
  [Fintype E]
  [DecidableEq E]
  {n t : ℕ} :
-- imply
  MeasurePreserving (sp1_tailDisint n t) (ubfTail n t) ((ubfTail n (t+1)).prod (Measure.pi (fun _ : sp1_Sing n t => unitMeasure))) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.sp1_tailSplit_mp n t

/--
[sp1_headExtC_meas](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/SpliceST1.lean)
-/
@[path]
private lemma sp1_headExtC_meas_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {t : ℕ}
-- given
  (htn : t < n)
  (A : {i : Fin n // (i:ℕ) < t} → ℝ) :
-- imply
  Measurable (fun c : sp1_Sing n t → ℝ => sp1_headExtC t htn A c) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.sp1_headExtC_meas t htn A

/--
[sp1_acp_join_compat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/SpliceST1.lean)
-/
@[path]
private lemma sp1_acp_join_compat_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {t : ℕ}
-- given
  (htn : t < n)
  (A : {i : Fin n // (i:ℕ) < t} → ℝ)
  (B : {i : Fin n // ¬ (i:ℕ) < t} → ℝ) :
-- imply
  acp_join t A B = acp_join (t+1) (sp1_headExtC t htn A ((sp1_tailDisint n t B).2)) ((sp1_tailDisint n t B).1) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.sp1_acp_join_compat t htn A B

/--
[sp1_reshuf_mp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/SpliceST1.lean)
-/
@[path]
private lemma sp1_reshuf_mp_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {t : ℕ} :
-- imply
  MeasurePreserving (sp1_reshuf (n := n) t) ((ubfTail n t).prod (Vcube n)) ((Measure.pi (fun _ : sp1_Sing n t => unitMeasure)).prod ((ubfTail n (t+1)).prod (Vcube n))) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.sp1_reshuf_mp t

/--
[sp1_reshuf_meas](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/SpliceST1.lean)
-/
@[path]
private lemma sp1_reshuf_meas_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {t : ℕ} :
-- imply
  Measurable (sp1_reshuf (n := n) t) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.sp1_reshuf_meas t

/--
[sp1_selRand_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/SpliceST1.lean)
-/
@[path]
private lemma sp1_selRand_factor_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {t : ℕ}
-- given
  (htn : t < n)
  (A : {i : Fin n // (i:ℕ) < t} → ℝ) :
-- imply
  atl_selRand μ σ f t (t+1) A = (Function.uncurry (sp1_G μ σ f t htn A)) ∘ (sp1_reshuf (n := n) t) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.sp1_selRand_factor μ σ f t htn A

/--
[sp1_G_uncurry_meas](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/SpliceST1.lean)
-/
@[path]
private lemma sp1_G_uncurry_meas_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {t : ℕ}
-- given
  (htn : t < n)
  (A : {i : Fin n // (i:ℕ) < t} → ℝ) :
-- imply
  Measurable (Function.uncurry (sp1_G μ σ f t htn A)) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.sp1_G_uncurry_meas μ σ f t htn A

/--
[sp1_tailSelMP](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/SpliceST1.lean)
-/
@[path]
private lemma sp1_tailSelMP_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {t : ℕ}
-- given
  (htn : t < n)
  (A : {i : Fin n // (i:ℕ) < t} → ℝ) :
-- imply
  atl_TailSelMP μ σ f t (t+1) A := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.sp1_tailSelMP μ σ f t htn A

/--
[sp1_restrictedSum_of_tailSelMP](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/SpliceST1.lean)
-/
@[path]
private lemma sp1_restrictedSum_of_tailSelMP_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {t s : ℕ}
-- given
  (A : {i : Fin n // (i:ℕ) < t} → ℝ)
  (hMP : atl_TailSelMP μ σ f t s A) :
-- imply
  tsm_TailSelMP_restrictedSum μ σ f t s A := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.sp1_restrictedSum_of_tailSelMP μ σ f t s A hMP

/--
[sp1_restrictedSum_at_s_eq_t_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/SpliceST1.lean)
-/
@[path]
private lemma sp1_restrictedSum_at_s_eq_t_succ_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {t : ℕ}
-- given
  (htn : t < n)
  (A : {i : Fin n // (i:ℕ) < t} → ℝ) :
-- imply
  tsm_TailSelMP_restrictedSum μ σ f t (t+1) A := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.sp1_restrictedSum_at_s_eq_t_succ μ σ f t htn A


-- created on 2026-10-23
