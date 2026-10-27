import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.OSSS.OptionalStopping.Part3
open Finset MeasureTheory StatMech StatMech.OSSS StatMech.OSSS.AdaptDisintegration


/--
[osp_tailSelFixed_meas](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/OptionalStopping.lean)
-/
@[path]
private lemma osp_tailSelFixed_meas_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {t s k : ℕ}
-- given
  (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
-- imply
  Measurable (osp_tailSelFixed t s k A) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.osp_tailSelFixed_meas t s k A

/--
[osp_proj_meas](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/OptionalStopping.lean)
-/
@[path]
private lemma osp_proj_meas_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {t : ℕ} :
-- imply
  Measurable (osp_proj (n := n) t) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.osp_proj_meas t

/--
[osp_proj_measurePreserving](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/OptionalStopping.lean)
-/
@[path]
private lemma osp_proj_measurePreserving_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {t : ℕ} :
-- imply
  MeasurePreserving (osp_proj (n := n) t) (((ubfHead n t).prod (ubfTail n t)).prod (Vcube n)) ((ubfTail n t).prod (Vcube n)) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.osp_proj_measurePreserving t

/--
[osp_fill_measurePreserving](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/OptionalStopping.lean)
-/
@[path]
private lemma osp_fill_measurePreserving_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {t s k : ℕ} :
-- imply
  MeasurePreserving (osp_fill (n := n) t s k) (((ubfHead n t).prod (ubfTail n t)).prod (Vcube n)) (Vcube n) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.osp_fill_measurePreserving t s k

/--
[osp_fill_eq_tailSel_comp_proj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/OptionalStopping.lean)
-/
@[path]
private lemma osp_fill_eq_tailSel_comp_proj_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {t s k : ℕ}
-- given
  (hts : t ≤ s)
  (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
-- imply
  osp_fill (n := n) t s k = (osp_tailSelFixed t s k A) ∘ (osp_proj (n := n) t) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.osp_fill_eq_tailSel_comp_proj t s k hts A

/--
[osp_tailSelFixed_mp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/OptionalStopping.lean)
-/
@[path]
private lemma osp_tailSelFixed_mp_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {t s k : ℕ}
-- given
  (hts : t ≤ s)
  (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
-- imply
  MeasurePreserving (osp_tailSelFixed t s k A) ((ubfTail n t).prod (Vcube n)) (Vcube n) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.osp_tailSelFixed_mp t s k hts A

/--
[osp_tailSelFixed_law](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/OptionalStopping.lean)
-/
@[path]
private lemma osp_tailSelFixed_law_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {g : ConfigSpace E → ℝ}
  {Cg : ℝ}
  {t s k : ℕ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hgC : ∀ ω, |g ω| ≤ Cg)
  (hts : t ≤ s)
  (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
-- imply
  (∫ B, (∫ V, g (codeMap μ (σ : Fin n → E) (adaptWt (acp_join t A B) V k s)) ∂(Vcube n)) ∂(ubfTail n t)) = Lindeberg.mean μ g := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.osp_tailSelFixed_law μ hpos hμ1 σ g hgC t s k hts A

/--
[osp_tailSelMP_of_const_switch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/OptionalStopping.lean)
-/
@[path]
private lemma osp_tailSelMP_of_const_switch_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {t s : ℕ}
  {k₀ : ℕ}
-- given
  (hts : t ≤ s)
  (A : {i : Fin n // (i : ℕ) < t} → ℝ)
  (hconst : ∀ B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ, stopVal μ σ f (acp_join t A B) = k₀) :
-- imply
  atl_TailSelMP μ σ f t s A := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.osp_tailSelMP_of_const_switch μ σ t s hts A k₀ hconst

/--
[osp_naive_per_partition_glue_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/OptionalStopping.lean)
-/
@[path]
private lemma osp_naive_per_partition_glue_false_eq
  [Fintype E]
  [DecidableEq E] :
-- imply
  ¬ (∀ {Ω β : Type} [MeasurableSpace Ω] [MeasurableSpace β] (μ : Measure Ω) (ν : Measure β) (h₀ h₁ : Ω → β) (p : Ω → Prop) [DecidablePred p] (_h0 : MeasurePreserving h₀ μ ν) (_h1 : MeasurePreserving h₁ μ ν) (h : Ω → β) (_hpiece : ∀ x, h x = if p x then h₀ x else h₁ x), MeasurePreserving h μ ν) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.osp_naive_per_partition_glue_false


-- created on 2026-10-23
