import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.OSSS.TailCondLawClose
open Finset MeasureTheory StatMech StatMech.OSSS StatMech.OSSS.AdaptDisintegration


/--
[atl_jointMeas](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailCondLawClose.lean)
-/
@[path]
private lemma atl_jointMeas_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f g : ConfigSpace E → ℝ}
  {t s : ℕ}
-- given
  (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
-- imply
  Measurable (fun p : ({i : Fin n // ¬ (i : ℕ) < t} → ℝ) × (Fin n → ℝ) => g (codeMap μ (σ : Fin n → E) (atl_selRand μ σ f t s A p))) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.atl_jointMeas μ σ f g t s A

/--
[atl_tailSelMP_of_stop_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailCondLawClose.lean)
-/
@[path]
private lemma atl_tailSelMP_of_stop_le_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {t s : ℕ}
-- given
  (A : {i : Fin n // (i : ℕ) < t} → ℝ)
  (hstop : ∀ B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ, stopVal μ σ f (acp_join t A B) ≤ s) :
-- imply
  atl_TailSelMP μ σ f t s A := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.atl_tailSelMP_of_stop_le σ t s A hstop

/--
[atl_innerRand_eq_mean](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailCondLawClose.lean)
-/
@[path]
private lemma atl_innerRand_eq_mean_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {g : ConfigSpace E → ℝ}
  {Cg : ℝ}
  {t s : ℕ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hgC : ∀ ω, |g ω| ≤ Cg)
  (A : {i : Fin n // (i : ℕ) < t} → ℝ)
  (hMP : atl_TailSelMP μ σ f t s A) :
-- imply
  (∫ B, (∫ V, g (codeMap μ (σ : Fin n → E) (adaptWt (acp_join t A B) V (stopVal μ σ f (acp_join t A B)) s)) ∂(Vcube n)) ∂(ubfTail n t)) = Lindeberg.mean μ g := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.atl_innerRand_eq_mean μ hpos hμ1 σ g hgC t s A hMP

/--
[atl_diag_of_MP](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailCondLawClose.lean)
-/
@[path]
private lemma atl_diag_of_MP_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {e : E}
  {t s : ℕ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hfC : ∀ ω, |f ω| ≤ 1)
  (A : {i : Fin n // (i : ℕ) < t} → ℝ)
  (hMP : atl_TailSelMP μ σ f t s A) :
-- imply
  (∫ B, fiberDiag μ σ f e s (acp_join t A B) ∂(ubfTail n t)) = Lindeberg.mean μ (fun ω => f ω * Lindeberg.coord e ω) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.atl_diag_of_MP μ hpos hμ1 σ hfC e t s A hMP

/--
[atl_margRand_meas](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailCondLawClose.lean)
-/
@[path]
private lemma atl_margRand_meas_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f g : ConfigSpace E → ℝ}
  {t s : ℕ}
-- given
  (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
-- imply
  Measurable (atl_margRand μ σ f g t s A) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.atl_margRand_meas μ σ f g t s A

/--
[atl_margRand_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailCondLawClose.lean)
-/
@[path]
private lemma atl_margRand_le_one_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f g : ConfigSpace E → ℝ}
  {t s : ℕ}
-- given
  (hgC : ∀ ω, |g ω| ≤ 1)
  (A : {i : Fin n // (i : ℕ) < t} → ℝ)
  (B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ) :
-- imply
  |atl_margRand μ σ f g t s A B| ≤ 1 := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.atl_margRand_le_one μ σ f g hgC t s A B

/--
[atl_marg_of_MP](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailCondLawClose.lean)
-/
@[path]
private lemma atl_marg_of_MP_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {g : ConfigSpace E → ℝ}
  {Cg : ℝ}
  {t s : ℕ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hgC : ∀ ω, |g ω| ≤ Cg)
  (A : {i : Fin n // (i : ℕ) < t} → ℝ)
  (hMP : atl_TailSelMP μ σ f t s A) :
-- imply
  (∫ B, atl_margRand μ σ f g t s A B ∂(ubfTail n t)) = Lindeberg.mean μ g := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.atl_marg_of_MP μ hpos hμ1 σ g hgC t s A hMP

/--
[atl_margMonoRand_of_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailCondLawClose.lean)
-/
@[path]
private lemma atl_margMonoRand_of_const_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f g : ConfigSpace E → ℝ}
  {Cg : ℝ}
  {t s : ℕ}
  {m₀ : ℕ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hmono : IsMonotonicMeasure μ)
  (hg : Monotone g)
  (hgC : ∀ ω, |g ω| ≤ Cg)
  (A : {i : Fin n // (i : ℕ) < t} → ℝ)
  (hconst : ∀ B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ, stopVal μ σ f (acp_join t A B) = m₀) :
-- imply
  atl_MargMonoRand μ σ f g t s A := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.atl_margMonoRand_of_const hpos hmono σ hg hgC t s A m₀ hconst

/--
[atl_cross_of_MP_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailCondLawClose.lean)
-/
@[path]
private lemma atl_cross_of_MP_mono_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {e : E}
  {t s₁ s₂ : ℕ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hfC : ∀ ω, |f ω| ≤ 1)
  (A : {i : Fin n // (i : ℕ) < t} → ℝ)
  (hMP1 : atl_TailSelMP μ σ f t s₁ A)
  (hMP2 : atl_TailSelMP μ σ f t s₂ A)
  (hmono1 : atl_MargMonoRand μ σ f f t s₁ A)
  (hmono2 : atl_MargMonoRand μ σ f (Lindeberg.coord e) t s₂ A) :
-- imply
  Lindeberg.mean μ f * Lindeberg.mean μ (Lindeberg.coord e) ≤ ∫ B, fiberCross μ σ f e s₁ s₂ (acp_join t A B) ∂(ubfTail n t) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.atl_cross_of_MP_mono μ hpos hμ1 σ hfC e t s₁ s₂ A hMP1 hMP2 hmono1 hmono2

/--
[atl_tailCondLaw_of_residues](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailCondLawClose.lean)
-/
@[path]
private lemma atl_tailCondLaw_of_residues_eq
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
  (hMP : ∀ (t : ℕ) (s : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ), atl_TailSelMP μ σ f t s A)
  (hMono : ∀ (t s : ℕ) (g : ConfigSpace E → ℝ) (A : {i : Fin n // (i : ℕ) < t} → ℝ), atl_MargMonoRand μ σ f g t s A) :
-- imply
  acp_TailCondLaw μ σ f := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.atl_tailCondLaw_of_residues hpos hμ1 σ hfC hMP hMono

/--
[atl_fiberDiag_eq_fixed_of_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailCondLawClose.lean)
-/
@[path]
private lemma atl_fiberDiag_eq_fixed_of_const_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {e : E}
  {t s : ℕ}
  {m₀ : ℕ}
-- given
  (A : {i : Fin n // (i : ℕ) < t} → ℝ)
  (hconst : ∀ B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ, stopVal μ σ f (acp_join t A B) = m₀)
  (B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ) :
-- imply
  fiberDiag μ σ f e s (acp_join t A B) = atc_fiberDiagFixed μ σ f e m₀ s (acp_join t A B) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.atl_fiberDiag_eq_fixed_of_const μ σ e t s A m₀ hconst B

/--
[atl_fiberCross_eq_fixed_of_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailCondLawClose.lean)
-/
@[path]
private lemma atl_fiberCross_eq_fixed_of_const_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {e : E}
  {t s₁ s₂ : ℕ}
  {m₀ : ℕ}
-- given
  (A : {i : Fin n // (i : ℕ) < t} → ℝ)
  (hconst : ∀ B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ, stopVal μ σ f (acp_join t A B) = m₀)
  (B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ) :
-- imply
  fiberCross μ σ f e s₁ s₂ (acp_join t A B) = atc_fiberCrossFixed μ σ f e m₀ s₁ s₂ (acp_join t A B) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.atl_fiberCross_eq_fixed_of_const μ σ e t s₁ s₂ A m₀ hconst B

/--
[atl_tailCondLaw_const_switch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailCondLawClose.lean)
-/
@[path]
private lemma atl_tailCondLaw_const_switch_eq
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
  (atl_const : ∀ (t : ℕ), ({i : Fin n // (i : ℕ) < t} → ℝ) → ℕ)
  (hconst : ∀ (t : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ) (B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ), stopVal μ σ f (acp_join t A B) = atl_const t A) :
-- imply
  acp_TailCondLaw μ σ f := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.atl_tailCondLaw_const_switch hpos hμ1 hmono σ hf hfC atl_const hconst


-- created on 2026-10-23
