import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.OSSS.TailCondLaw
open Finset MeasureTheory StatMech StatMech.OSSS StatMech.OSSS.AdaptDisintegration


/--
[atc_adaptWt_join_indep_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailCondLaw.lean)
-/
@[path]
private lemma atc_adaptWt_join_indep_head_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {t s m : ℕ}
  {V : Fin n → ℝ}
-- given
  (hst : t ≤ s)
  (A A' : {i : Fin n // (i : ℕ) < t} → ℝ)
  (B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ) :
-- imply
  adaptWt (acp_join t A B) V m s = adaptWt (acp_join t A' B) V m s := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.atc_adaptWt_join_indep_head t s m hst A A' B V

/--
[atc_innerFixed_const_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailCondLaw.lean)
-/
@[path]
private lemma atc_innerFixed_const_head_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {g : ConfigSpace E → ℝ}
  {t s m : ℕ}
-- given
  (hst : t ≤ s)
  (A A' : {i : Fin n // (i : ℕ) < t} → ℝ) :
-- imply
  atc_innerFixed μ σ g t A m s = atc_innerFixed μ σ g t A' m s := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.atc_innerFixed_const_head μ σ g t s m hst A A'

/--
[atc_avg_innerFixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailCondLaw.lean)
-/
@[path]
private lemma atc_avg_innerFixed_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {g : ConfigSpace E → ℝ}
  {Cg : ℝ}
  {t m s : ℕ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hgC : ∀ ω, |g ω| ≤ Cg) :
-- imply
  (∫ A, atc_innerFixed μ σ g t A m s ∂(ubfHead n t)) = ∑ x, g x * μ x := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.atc_avg_innerFixed μ hpos hμ1 σ hgC t m s

/--
[atc_innerFixed_eq_mean](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailCondLaw.lean)
-/
@[path]
private lemma atc_innerFixed_eq_mean_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {g : ConfigSpace E → ℝ}
  {Cg : ℝ}
  {t s m : ℕ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hgC : ∀ ω, |g ω| ≤ Cg)
  (hst : t ≤ s)
  (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
-- imply
  atc_innerFixed μ σ g t A m s = Lindeberg.mean μ g := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.atc_innerFixed_eq_mean μ hpos hμ1 σ hgC t s m hst A

/--
[atc_tailCondLawFixedDiag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailCondLaw.lean)
-/
@[path]
private lemma atc_tailCondLawFixedDiag_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {e : E}
  {t s m : ℕ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hfC : ∀ ω, |f ω| ≤ 1)
  (hst : t ≤ s)
  (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
-- imply
  (∫ B, atc_fiberDiagFixed μ σ f e m s (acp_join t A B) ∂(ubfTail n t)) = Lindeberg.mean μ (fun ω => f ω * Lindeberg.coord e ω) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.atc_tailCondLawFixedDiag μ hpos hμ1 σ hfC e t s m hst A

/--
[atc_tailCondLawFixedMarg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailCondLaw.lean)
-/
@[path]
private lemma atc_tailCondLawFixedMarg_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {g : ConfigSpace E → ℝ}
  {Cg : ℝ}
  {t s m : ℕ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hgC : ∀ ω, |g ω| ≤ Cg)
  (hst : t ≤ s)
  (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
-- imply
  (∫ B, atc_fiberMargFixed μ σ g m s (acp_join t A B) ∂(ubfTail n t)) = Lindeberg.mean μ g := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.atc_tailCondLawFixedMarg μ hpos hμ1 σ hgC t s m hst A

/--
[atc_hasFKG_ubfTail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailCondLaw.lean)
-/
@[path]
private lemma atc_hasFKG_ubfTail_eq
  [Fintype E]
  [DecidableEq E]
  {n t : ℕ} :
-- imply
  HasFKG (ubfTail n t) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.atc_hasFKG_ubfTail n t

/--
[atc_joint_meas_BV](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailCondLaw.lean)
-/
@[path]
private lemma atc_joint_meas_BV_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {g : ConfigSpace E → ℝ}
  {t m s : ℕ}
-- given
  (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
-- imply
  Measurable (fun p : ({i : Fin n // ¬ (i : ℕ) < t} → ℝ) × (Fin n → ℝ) => g (codeMap μ (σ : Fin n → E) (adaptWt (acp_join t A p.1) p.2 m s))) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.atc_joint_meas_BV μ σ g t m s A

/--
[atc_marg_meas_B](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailCondLaw.lean)
-/
@[path]
private lemma atc_marg_meas_B_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {g : ConfigSpace E → ℝ}
  {t m s : ℕ}
-- given
  (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
-- imply
  Measurable (fun B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ => ∫ V, g (codeMap μ (σ : Fin n → E) (adaptWt (acp_join t A B) V m s)) ∂(Vcube n)) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.atc_marg_meas_B μ σ g t m s A

/--
[atc_marg_mono_B](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailCondLaw.lean)
-/
@[path]
private lemma atc_marg_mono_B_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {g : ConfigSpace E → ℝ}
  {Cg : ℝ}
  {t m s : ℕ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hmono : IsMonotonicMeasure μ)
  (hg : Monotone g)
  (hgC : ∀ ω, |g ω| ≤ Cg)
  (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
-- imply
  Monotone (fun B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ => ∫ V, g (codeMap μ (σ : Fin n → E) (adaptWt (acp_join t A B) V m s)) ∂(Vcube n)) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.atc_marg_mono_B hpos hmono σ hg hgC t m s A

/--
[atc_marg_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailCondLaw.lean)
-/
@[path]
private lemma atc_marg_le_one_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {g : ConfigSpace E → ℝ}
  {t m s : ℕ}
-- given
  (hgC : ∀ ω, |g ω| ≤ 1)
  (A : {i : Fin n // (i : ℕ) < t} → ℝ)
  (B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ) :
-- imply
  |∫ V, g (codeMap μ (σ : Fin n → E) (adaptWt (acp_join t A B) V m s)) ∂(Vcube n)| ≤ 1 := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.atc_marg_le_one μ σ hgC t m s A B

/--
[atc_tailCondLawFixedCross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailCondLaw.lean)
-/
@[path]
private lemma atc_tailCondLawFixedCross_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {e : E}
  {t s₁ s₂ m : ℕ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hmono : IsMonotonicMeasure μ)
  (hf : Monotone f)
  (hfC : ∀ ω, |f ω| ≤ 1)
  (hst1 : t ≤ s₁)
  (hst2 : t ≤ s₂)
  (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
-- imply
  Lindeberg.mean μ f * Lindeberg.mean μ (Lindeberg.coord e) ≤ ∫ B, atc_fiberCrossFixed μ σ f e m s₁ s₂ (acp_join t A B) ∂(ubfTail n t) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.atc_tailCondLawFixedCross hpos hμ1 hmono σ hf hfC e t s₁ s₂ m hst1 hst2 A

/--
[atc_tailCondLawFixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailCondLaw.lean)
-/
@[path]
private lemma atc_tailCondLawFixed_eq
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
  (hfC : ∀ ω, |f ω| ≤ 1) :
-- imply
  atc_TailCondLawFixed μ σ f := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.atc_tailCondLawFixed hpos hμ1 hmono σ hf hfC


-- created on 2026-10-23
