import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.OSSS.AdaptDisintegration
open Finset MeasureTheory StatMech StatMech.OSSS StatMech.OSSS.AdaptDisintegration


/--
[sw2_invol](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptDisintegration.lean)
-/
@[path]
private lemma sw2_invol_eq
  [Fintype E]
  [DecidableEq E]
  {n s m : ℕ} :
-- imply
  Function.Involutive (sw2 n s m) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.sw2_invol n s m

/--
[sw2Equiv_symm_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptDisintegration.lean)
-/
@[path]
private lemma sw2Equiv_symm_apply_eq
  [Fintype E]
  [DecidableEq E]
  {n s m : ℕ}
  {x : Fin n ⊕ Fin n} :
-- imply
  (sw2Equiv n s m).symm x = sw2 n s m x := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.sw2Equiv_symm_apply n s m x

/--
[adsD_selMap2_eq_adaptWt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptDisintegration.lean)
-/
@[path]
private lemma adsD_selMap2_eq_adaptWt_eq
  [Fintype E]
  [DecidableEq E]
  {n s m : ℕ}
  {U V : Fin n → ℝ} :
-- imply
  selMap2 n s m (U, V) = adaptWt U V m s := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.adsD_selMap2_eq_adaptWt n s m U V

/--
[adsD_selMap2_measurePreserving](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptDisintegration.lean)
-/
@[path]
private lemma adsD_selMap2_measurePreserving_eq
  [Fintype E]
  [DecidableEq E]
  {n s m : ℕ} :
-- imply
  MeasurePreserving (selMap2 n s m) ((Vcube n).prod (Vcube n)) (Vcube n) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.adsD_selMap2_measurePreserving n s m

/--
[adsD_integral_g_adaptWt_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptDisintegration.lean)
-/
@[path]
private lemma adsD_integral_g_adaptWt_fixed_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {g : ConfigSpace E → ℝ}
  {s m : ℕ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  ∫ p, g (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 m s)) ∂((Vcube n).prod (Vcube n)) = ∑ x, g x * μ x := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.adsD_integral_g_adaptWt_fixed μ hpos hμ1 σ g s m

/--
[adsD_measurable_f_adaptWt_fiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptDisintegration.lean)
-/
@[path]
private lemma adsD_measurable_f_adaptWt_fiber_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {U : Fin n → ℝ}
  {m s : ℕ} :
-- imply
  Measurable (fun V : Fin n → ℝ => f (codeMap μ (σ : Fin n → E) (adaptWt U V m s))) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.adsD_measurable_f_adaptWt_fiber μ σ f U m s

/--
[adsD_measurable_f_adaptWt_prod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptDisintegration.lean)
-/
@[path]
private lemma adsD_measurable_f_adaptWt_prod_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {g : ConfigSpace E → ℝ}
  {m s : ℕ} :
-- imply
  Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => g (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 m s))) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.adsD_measurable_f_adaptWt_prod μ σ g m s

/--
[adsD_adaptWt_mono_V](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptDisintegration.lean)
-/
@[path]
private lemma adsD_adaptWt_mono_V_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {U : Fin n → ℝ}
  {m s : ℕ} :
-- imply
  Monotone (fun V : Fin n → ℝ => adaptWt U V m s) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.adsD_adaptWt_mono_V U m s

/--
[adsD_f_adaptWt_mono_V](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptDisintegration.lean)
-/
@[path]
private lemma adsD_f_adaptWt_mono_V_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n → E}
  {f : ConfigSpace E → ℝ}
  {U : Fin n → ℝ}
  {m s : ℕ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hmono : IsMonotonicMeasure μ)
  (hf : Monotone f) :
-- imply
  Monotone (fun V : Fin n → ℝ => f (codeMap μ σ (adaptWt U V m s))) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.adsD_f_adaptWt_mono_V hpos hmono σ hf U m s

/--
[adsD_coord_adaptWt_mono_V](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptDisintegration.lean)
-/
@[path]
private lemma adsD_coord_adaptWt_mono_V_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n → E}
  {e : E}
  {U : Fin n → ℝ}
  {m s : ℕ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hmono : IsMonotonicMeasure μ) :
-- imply
  Monotone (fun V : Fin n → ℝ => Lindeberg.coord e (codeMap μ σ (adaptWt U V m s))) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.adsD_coord_adaptWt_mono_V hpos hmono σ e U m s

/--
[adsD_integrable_prod_obs_fiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptDisintegration.lean)
-/
@[path]
private lemma adsD_integrable_prod_obs_fiber_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {Cf : ℝ}
  {e : E}
  {U : Fin n → ℝ}
  {m s₁ s₂ : ℕ}
-- given
  (hfC : ∀ ω, |f ω| ≤ Cf) :
-- imply
  Integrable (fun V : Fin n → ℝ => f (codeMap μ (σ : Fin n → E) (adaptWt U V m s₁)) * Lindeberg.coord e (codeMap μ (σ : Fin n → E) (adaptWt U V m s₂))) (Vcube n) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.adsD_integrable_prod_obs_fiber μ σ hfC e U m s₁ s₂

/--
[adsD_abs_adapt_step_eq_four_terms](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptDisintegration.lean)
-/
@[path]
private lemma adsD_abs_adapt_step_eq_four_terms_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {t m : ℕ}
  {U V : Fin n → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hmono : IsMonotonicMeasure μ)
  (hf : Monotone f)
  (ht : 1 ≤ t)
  (htm : t ≤ m)
  (htn : t - 1 < n) :
-- imply
  |f (codeMap μ (σ : Fin n → E) (adaptWt U V m t)) - f (codeMap μ (σ : Fin n → E) (adaptWt U V m (t-1)))| = f (codeMap μ (σ : Fin n → E) (adaptWt U V m (t-1))) * Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩) (codeMap μ (σ : Fin n → E) (adaptWt U V m (t-1))) + f (codeMap μ (σ : Fin n → E) (adaptWt U V m t)) * Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩) (codeMap μ (σ : Fin n → E) (adaptWt U V m t)) - f (codeMap μ (σ : Fin n → E) (adaptWt U V m (t-1))) * Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩) (codeMap μ (σ : Fin n → E) (adaptWt U V m t)) - f (codeMap μ (σ : Fin n → E) (adaptWt U V m t)) * Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩) (codeMap μ (σ : Fin n → E) (adaptWt U V m (t-1))) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.adsD_abs_adapt_step_eq_four_terms hpos hmono σ hf t m ht htm htn U V

/--
[adsD_abs_adapt_step_integral_fiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptDisintegration.lean)
-/
@[path]
private lemma adsD_abs_adapt_step_integral_fiber_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {Cf : ℝ}
  {t m : ℕ}
  {U : Fin n → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hmono : IsMonotonicMeasure μ)
  (hf : Monotone f)
  (hfC : ∀ ω, |f ω| ≤ Cf)
  (ht : 1 ≤ t)
  (htm : t ≤ m)
  (htn : t - 1 < n) :
-- imply
  (∫ V, |f (codeMap μ (σ : Fin n → E) (adaptWt U V m t)) - f (codeMap μ (σ : Fin n → E) (adaptWt U V m (t-1)))| ∂(Vcube n)) = (∫ V, f (codeMap μ (σ : Fin n → E) (adaptWt U V m (t-1))) * Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩) (codeMap μ (σ : Fin n → E) (adaptWt U V m (t-1))) ∂(Vcube n)) + (∫ V, f (codeMap μ (σ : Fin n → E) (adaptWt U V m t)) * Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩) (codeMap μ (σ : Fin n → E) (adaptWt U V m t)) ∂(Vcube n)) - (∫ V, f (codeMap μ (σ : Fin n → E) (adaptWt U V m (t-1))) * Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩) (codeMap μ (σ : Fin n → E) (adaptWt U V m t)) ∂(Vcube n)) - (∫ V, f (codeMap μ (σ : Fin n → E) (adaptWt U V m t)) * Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩) (codeMap μ (σ : Fin n → E) (adaptWt U V m (t-1))) ∂(Vcube n)) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.adsD_abs_adapt_step_integral_fiber hpos hmono σ hf hfC t m ht htm htn U

/--
[adsD_adapt_fkg_cross_fiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptDisintegration.lean)
-/
@[path]
private lemma adsD_adapt_fkg_cross_fiber_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {Cf : ℝ}
  {e : E}
  {m s₁ s₂ : ℕ}
  {U : Fin n → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hmono : IsMonotonicMeasure μ)
  (hf : Monotone f)
  (hfC : ∀ ω, |f ω| ≤ Cf) :
-- imply
  (∫ V, f (codeMap μ (σ : Fin n → E) (adaptWt U V m s₁)) ∂(Vcube n)) * (∫ V, Lindeberg.coord e (codeMap μ (σ : Fin n → E) (adaptWt U V m s₂)) ∂(Vcube n)) ≤ ∫ V, f (codeMap μ (σ : Fin n → E) (adaptWt U V m s₁)) * Lindeberg.coord e (codeMap μ (σ : Fin n → E) (adaptWt U V m s₂)) ∂(Vcube n) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.adsD_adapt_fkg_cross_fiber hpos hmono σ hf hfC e m s₁ s₂ U

/--
[adsD_adapt_step_fiber_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptDisintegration.lean)
-/
@[path]
private lemma adsD_adapt_step_fiber_le_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {Cf : ℝ}
  {t m : ℕ}
  {U : Fin n → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hmono : IsMonotonicMeasure μ)
  (hf : Monotone f)
  (hfC : ∀ ω, |f ω| ≤ Cf)
  (ht : 1 ≤ t)
  (htm : t ≤ m)
  (htn : t - 1 < n) :
-- imply
  (∫ V, |f (codeMap μ (σ : Fin n → E) (adaptWt U V m t)) - f (codeMap μ (σ : Fin n → E) (adaptWt U V m (t-1)))| ∂(Vcube n)) ≤ (∫ V, f (codeMap μ (σ : Fin n → E) (adaptWt U V m (t-1))) * Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩) (codeMap μ (σ : Fin n → E) (adaptWt U V m (t-1))) ∂(Vcube n)) + (∫ V, f (codeMap μ (σ : Fin n → E) (adaptWt U V m t)) * Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩) (codeMap μ (σ : Fin n → E) (adaptWt U V m t)) ∂(Vcube n)) - (∫ V, f (codeMap μ (σ : Fin n → E) (adaptWt U V m (t-1))) ∂(Vcube n)) * (∫ V, Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩) (codeMap μ (σ : Fin n → E) (adaptWt U V m t)) ∂(Vcube n)) - (∫ V, f (codeMap μ (σ : Fin n → E) (adaptWt U V m t)) ∂(Vcube n)) * (∫ V, Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩) (codeMap μ (σ : Fin n → E) (adaptWt U V m (t-1))) ∂(Vcube n)) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.adsD_adapt_step_fiber_le hpos hmono σ hf hfC t m ht htm htn U

/--
[truncInd_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptDisintegration.lean)
-/
@[path]
private lemma truncInd_nonneg_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {U : Fin n → ℝ}
  {t : ℕ} :
-- imply
  0 ≤ truncInd μ σ f U t := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.truncInd_nonneg μ σ f U t

/--
[adsD_fubini_lhs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptDisintegration.lean)
-/
@[path]
private lemma adsD_fubini_lhs_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {t : ℕ}
-- given
  (hfC : ∀ ω, |f ω| ≤ 1) :
-- imply
  (∫ p, |f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) (t+1))) - f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) t))| * truncInd μ σ f p.1 (t + 1) ∂((Vcube n).prod (Vcube n))) = ∫ U, fiberStep μ σ f t U * truncInd μ σ f U (t+1) ∂(Vcube n) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.adsD_fubini_lhs μ σ hfC t

/--
[adsD_integrable_fiberStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptDisintegration.lean)
-/
@[path]
private lemma adsD_integrable_fiberStep_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {t : ℕ}
-- given
  (hfC : ∀ ω, |f ω| ≤ 1) :
-- imply
  Integrable (fun U => fiberStep μ σ f t U * truncInd μ σ f U (t+1)) (Vcube n) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.adsD_integrable_fiberStep μ σ hfC t

/--
[adsD_integrable_fiberDiag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptDisintegration.lean)
-/
@[path]
private lemma adsD_integrable_fiberDiag_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {e : E}
  {s : ℕ}
  {t : ℕ}
-- given
  (hfC : ∀ ω, |f ω| ≤ 1) :
-- imply
  Integrable (fun U => fiberDiag μ σ f e s U * truncInd μ σ f U (t+1)) (Vcube n) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.adsD_integrable_fiberDiag μ σ hfC e s t

/--
[adsD_integrable_fiberCross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptDisintegration.lean)
-/
@[path]
private lemma adsD_integrable_fiberCross_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {e : E}
  {s₁ s₂ : ℕ}
  {t : ℕ}
-- given
  (hfC : ∀ ω, |f ω| ≤ 1) :
-- imply
  Integrable (fun U => fiberCross μ σ f e s₁ s₂ U * truncInd μ σ f U (t+1)) (Vcube n) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.adsD_integrable_fiberCross μ σ hfC e s₁ s₂ t

/--
[adsD_adaptStepCovBound_of_condBBB](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptDisintegration.lean)
-/
@[path]
private lemma adsD_adaptStepCovBound_of_condBBB_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hmono : IsMonotonicMeasure μ)
  (hf : Monotone f)
  (hfC : ∀ ω, |f ω| ≤ 1)
  (hBBB : AdaptCondBBB μ σ f) :
-- imply
  AdaptMConditional.AdaptStepCovBound μ σ f := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.adsD_adaptStepCovBound_of_condBBB hpos hmono σ hf hfC hBBB

/--
[adsD_tree_osss_sharp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptDisintegration.lean)
-/
@[path]
private lemma adsD_tree_osss_sharp_eq
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
  (hf0 : 0 ≤ f)
  (hf1 : ∀ ω, f ω ≤ 1)
  (hBBB : AdaptCondBBB μ σ f) :
-- imply
  Lindeberg.var μ f ≤ ∑ e, AdaptMConditional.revealAdapt μ σ f e * Lindeberg.cov μ f (Lindeberg.coord e) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.adsD_tree_osss_sharp hpos hμ1 hmono σ hf hf0 hf1 hBBB

/--
[adsD_fk_q2_sharp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptDisintegration.lean)
-/
@[path]
private lemma adsD_fk_q2_sharp_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
  {n : ℕ}
  {σ : Fin n ≃ Sym2 V}
  {f : ConfigSpace (Sym2 V) → ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hf : Monotone f)
  (hf0 : 0 ≤ f)
  (hf1 : ∀ ω, f ω ≤ 1)
  (hBBB : AdaptCondBBB (fkMass G p 2) σ f) :
-- imply
  Lindeberg.var (fkMass G p 2) f ≤ ∑ e, AdaptMConditional.revealAdapt (fkMass G p 2) σ f e * Lindeberg.cov (fkMass G p 2) f (Lindeberg.coord e) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.adsD_fk_q2_sharp G hp hp1 σ hf hf0 hf1 hBBB


-- created on 2026-10-23
