import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.OSSS.CrossVFKG.Part2
open Finset MeasureTheory StatMech StatMech.OSSS StatMech.OSSS.AdaptDisintegration


/--
[cvf_coord_local](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/CrossVFKG.lean)
-/
@[path]
private lemma cvf_coord_local_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {t : ℕ}
  {w w' : Fin n → ℝ}
-- given
  (htn : t < n)
  (h : ∀ i : Fin n, (i:ℕ) < t+1 → w i = w' i) :
-- imply
  codeMap μ (σ : Fin n → E) w ((σ : Fin n → E) ⟨t, htn⟩) = codeMap μ (σ : Fin n → E) w' ((σ : Fin n → E) ⟨t, htn⟩) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.cvf_coord_local μ σ t htn w w' h

/--
[cvf_coordMarg_const_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/CrossVFKG.lean)
-/
@[path]
private lemma cvf_coordMarg_const_succ_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {t : ℕ}
-- given
  (htn : t < n)
  (A : {i : Fin n // (i : ℕ) < t} → ℝ)
  (B B' : {i : Fin n // ¬ (i : ℕ) < t} → ℝ) :
-- imply
  atl_margRand μ σ f (Lindeberg.coord ((σ : Fin n → E) ⟨t, htn⟩)) t (t+1) A B = atl_margRand μ σ f (Lindeberg.coord ((σ : Fin n → E) ⟨t, htn⟩)) t (t+1) A B' := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.cvf_coordMarg_const_succ μ σ f t htn A B B'

/--
[cvf_cross_succ_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/CrossVFKG.lean)
-/
@[path]
private lemma cvf_cross_succ_eq_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {t : ℕ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hfC : ∀ ω, |f ω| ≤ 1)
  (htn : t < n)
  (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
-- imply
  (∫ B, fiberCross μ σ f ((σ : Fin n → E) ⟨t, htn⟩) t (t+1) (acp_join t A B) ∂(ubfTail n t)) = Lindeberg.mean μ f * Lindeberg.mean μ (Lindeberg.coord ((σ : Fin n → E) ⟨t, htn⟩)) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.cvf_cross_succ_eq μ hpos hμ1 σ hfC t htn A

/--
[cvf_cross_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/CrossVFKG.lean)
-/
@[path]
private lemma cvf_cross_succ_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {t : ℕ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hfC : ∀ ω, |f ω| ≤ 1)
  (htn : t < n)
  (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
-- imply
  Lindeberg.mean μ f * Lindeberg.mean μ (Lindeberg.coord ((σ : Fin n → E) ⟨t, htn⟩)) ≤ ∫ B, fiberCross μ σ f ((σ : Fin n → E) ⟨t, htn⟩) t (t+1) (acp_join t A B) ∂(ubfTail n t) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.cvf_cross_succ μ hpos hμ1 σ hfC t htn A

/--
[cvf_Cross41_of_margMono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/CrossVFKG.lean)
-/
@[path]
private lemma cvf_Cross41_of_margMono_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {t : ℕ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hfC : ∀ ω, |f ω| ≤ 1)
  (htn : t < n)
  (A : {i : Fin n // (i : ℕ) < t} → ℝ)
  (hmono1 : atl_MargMonoRand μ σ f f t (t+1) A)
  (hmono2 : atl_MargMonoRand μ σ f (Lindeberg.coord ((σ : Fin n → E) ⟨t, htn⟩)) t t A) :
-- imply
  cvf_Cross41 μ σ f t htn A := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.cvf_Cross41_of_margMono μ hpos hμ1 σ hfC t htn A hmono1 hmono2

/--
[cvf_Cross41_const_switch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/CrossVFKG.lean)
-/
@[path]
private lemma cvf_Cross41_const_switch_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {t : ℕ}
  {m₀ : ℕ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hmono : IsMonotonicMeasure μ)
  (hf : Monotone f)
  (hfC : ∀ ω, |f ω| ≤ 1)
  (htn : t < n)
  (A : {i : Fin n // (i : ℕ) < t} → ℝ)
  (hconst : ∀ B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ, stopVal μ σ f (acp_join t A B) = m₀) :
-- imply
  cvf_Cross41 μ σ f t htn A := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.cvf_Cross41_const_switch hpos hμ1 hmono σ hf hfC t htn A m₀ hconst

/--
[cvf_tailCondLaw_of_cross41](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/CrossVFKG.lean)
-/
@[path]
private lemma cvf_tailCondLaw_of_cross41_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hfC : ∀ ω, |f ω| ≤ 1)
  (hCross41 : ∀ (t : ℕ) (htn : t < n) (A : {i : Fin n // (i : ℕ) < t} → ℝ), cvf_Cross41 μ σ f t htn A) :
-- imply
  acp_TailCondLaw μ σ f := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.cvf_tailCondLaw_of_cross41 hpos hμ1 σ hfC hCross41

/--
[cvf_tailCondLaw_const_switch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/CrossVFKG.lean)
-/
@[path]
private lemma cvf_tailCondLaw_const_switch_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hmono : IsMonotonicMeasure μ)
  (hf : Monotone f)
  (hfC : ∀ ω, |f ω| ≤ 1)
  (cvf_const : ∀ (t : ℕ), ({i : Fin n // (i : ℕ) < t} → ℝ) → ℕ)
  (hconst : ∀ (t : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ) (B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ), stopVal μ σ f (acp_join t A B) = cvf_const t A) :
-- imply
  acp_TailCondLaw μ σ f := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.cvf_tailCondLaw_const_switch hpos hμ1 hmono σ hf hfC cvf_const hconst


-- created on 2026-10-23
