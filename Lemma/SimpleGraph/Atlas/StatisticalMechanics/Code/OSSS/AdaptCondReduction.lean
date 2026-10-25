import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.OSSS.AdaptCondReduction
open Finset MeasureTheory StatMech StatMech.OSSS StatMech.OSSS.AdaptDisintegration


/--
[otc_factor_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptCondReduction.lean)
-/
@[path]
private lemma otc_factor_step_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {t : ℕ}
  {G : (Fin n → ℝ) → ℝ}
  {CG : ℝ}
-- given
  (hGm : Measurable G)
  (hGC : ∀ U, |G U| ≤ CG) :
-- imply
  (∫ U, truncInd μ σ f U (t+1) * G U ∂(cube n)) = ∫ A, acp_truncHead μ σ f t A * (∫ B, G (acp_join t A B) ∂(ubfTail n t)) ∂(ubfHead n t) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.otc_factor_step μ σ f t hGm hGC

/--
[otc_truncHead_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptCondReduction.lean)
-/
@[path]
private lemma otc_truncHead_nonneg_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {t : ℕ}
-- given
  (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
-- imply
  0 ≤ acp_truncHead μ σ f t A := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.otc_truncHead_nonneg μ σ f t A

/--
[otc_delta_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptCondReduction.lean)
-/
@[path]
private lemma otc_delta_eq_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {t : ℕ} :
-- imply
  (∫ U, truncInd μ σ f U (t+1) ∂(cube n)) = ∫ A, acp_truncHead μ σ f t A ∂(ubfHead n t) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.otc_delta_eq μ σ f t

/--
[otc_diag_component](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptCondReduction.lean)
-/
@[path]
private lemma otc_diag_component_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {t : ℕ}
  {e : E}
  {s : ℕ}
-- given
  (hfC : ∀ ω, |f ω| ≤ 1)
  (hs : ∀ (A : {i : Fin n // (i : ℕ) < t} → ℝ), (∫ B, fiberDiag μ σ f e s (acp_join t A B) ∂(ubfTail n t)) = Lindeberg.mean μ (fun ω => f ω * Lindeberg.coord e ω)) :
-- imply
  (∫ U, fiberDiag μ σ f e s U * truncInd μ σ f U (t+1) ∂(cube n)) = Lindeberg.mean μ (fun ω => f ω * Lindeberg.coord e ω) * ∫ U, truncInd μ σ f U (t+1) ∂(cube n) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.otc_diag_component μ σ hfC t e s hs

/--
[otc_cross_component](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptCondReduction.lean)
-/
@[path]
private lemma otc_cross_component_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {t : ℕ}
  {e : E}
  {s₁ s₂ : ℕ}
-- given
  (hfC : ∀ ω, |f ω| ≤ 1)
  (hs : ∀ (A : {i : Fin n // (i : ℕ) < t} → ℝ), Lindeberg.mean μ f * Lindeberg.mean μ (Lindeberg.coord e) ≤ ∫ B, fiberCross μ σ f e s₁ s₂ (acp_join t A B) ∂(ubfTail n t)) :
-- imply
  Lindeberg.mean μ f * Lindeberg.mean μ (Lindeberg.coord e) * ∫ U, truncInd μ σ f U (t+1) ∂(cube n) ≤ ∫ U, fiberCross μ σ f e s₁ s₂ U * truncInd μ σ f U (t+1) ∂(cube n) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.otc_cross_component μ σ hfC t e s₁ s₂ hs

/--
[otc_adaptCondBBB_of_tailCondLaw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptCondReduction.lean)
-/
@[path]
private lemma otc_adaptCondBBB_of_tailCondLaw_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
-- given
  (hfC : ∀ ω, |f ω| ≤ 1)
  (hTCL : acp_TailCondLaw μ σ f) :
-- imply
  AdaptCondBBB μ σ f := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.otc_adaptCondBBB_of_tailCondLaw σ hfC hTCL


-- created on 2026-10-23
