import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.OSSS.AdaptMConditional.Part6
open Finset MeasureTheory StatMech StatMech.OSSS StatMech.OSSS.AdaptMConditional


/--
[adaptWt_eq_Wt_mix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptMConditional.lean)
-/
@[path]
private lemma adaptWt_eq_Wt_mix_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {U V : Fin n → ℝ}
  {m t : ℕ} :
-- imply
  adaptWt U V m t = Wt (mixUV U V m) V t := by
-- proof
  apply StatMech.OSSS.AdaptMConditional.adaptWt_eq_Wt_mix U V m t

/--
[adaptWt_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptMConditional.lean)
-/
@[path]
private lemma adaptWt_zero_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {U V : Fin n → ℝ}
  {m : ℕ} :
-- imply
  adaptWt U V m 0 = mixUV U V m := by
-- proof
  apply StatMech.OSSS.AdaptMConditional.adaptWt_zero U V m

/--
[adaptWt_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptMConditional.lean)
-/
@[path]
private lemma adaptWt_card_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {U V : Fin n → ℝ}
  {m : ℕ} :
-- imply
  adaptWt U V m n = V := by
-- proof
  apply StatMech.OSSS.AdaptMConditional.adaptWt_card U V m

/--
[adaptWt_ge_stop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptMConditional.lean)
-/
@[path]
private lemma adaptWt_ge_stop_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {U V : Fin n → ℝ}
  {m t : ℕ}
-- given
  (htm : m ≤ t) :
-- imply
  adaptWt U V m t = V := by
-- proof
  apply StatMech.OSSS.AdaptMConditional.adaptWt_ge_stop U V m t htm

/--
[adaptWt_agree_off](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptMConditional.lean)
-/
@[path]
private lemma adaptWt_agree_off_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {U V : Fin n → ℝ}
  {m t : ℕ}
-- given
  (ht : 1 ≤ t) :
-- imply
  ∀ i : Fin n, (i : ℕ) ≠ t - 1 → adaptWt U V m t i = adaptWt U V m (t-1) i := by
-- proof
  apply StatMech.OSSS.AdaptMConditional.adaptWt_agree_off U V m t ht

/--
[adaptWt_at_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptMConditional.lean)
-/
@[path]
private lemma adaptWt_at_pos_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {U V : Fin n → ℝ}
  {m t : ℕ}
-- given
  (ht : 1 ≤ t)
  (htm : t ≤ m)
  (htn : t - 1 < n) :
-- imply
  adaptWt U V m t ⟨t-1, htn⟩ = V ⟨t-1, htn⟩ ∧ adaptWt U V m (t-1) ⟨t-1, htn⟩ = U ⟨t-1, htn⟩ := by
-- proof
  apply StatMech.OSSS.AdaptMConditional.adaptWt_at_pos U V m t ht htm htn

/--
[detAtC_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptMConditional.lean)
-/
@[path]
private lemma detAtC_card_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {X : ConfigSpace E} :
-- imply
  detAtC (σ : Fin n → E) f X n := by
-- proof
  apply StatMech.OSSS.AdaptMConditional.detAtC_card σ f X

/--
[stopVal_eq_stopValC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptMConditional.lean)
-/
@[path]
private lemma stopVal_eq_stopValC_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {U : Fin n → ℝ} :
-- imply
  stopVal μ σ f U = stopValC σ f (codeMap μ (σ : Fin n → E) U) := by
-- proof
  apply StatMech.OSSS.AdaptMConditional.stopVal_eq_stopValC μ σ f U

/--
[stopVal_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptMConditional.lean)
-/
@[path]
private lemma stopVal_le_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {U : Fin n → ℝ} :
-- imply
  stopVal μ σ f U ≤ n := by
-- proof
  apply StatMech.OSSS.AdaptMConditional.stopVal_le μ σ f U

/--
[stopVal_determines](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptMConditional.lean)
-/
@[path]
private lemma stopVal_determines_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {U : Fin n → ℝ} :
-- imply
  detAtC (σ : Fin n → E) f (codeMap μ (σ : Fin n → E) U) (stopVal μ σ f U) := by
-- proof
  apply StatMech.OSSS.AdaptMConditional.stopVal_determines μ σ f U

/--
[codeMap_agree_on_prefix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptMConditional.lean)
-/
@[path]
private lemma codeMap_agree_on_prefix_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {w w' : Fin n → ℝ}
  {k : ℕ}
-- given
  (hagree : ∀ i : Fin n, (i : ℕ) < k → w i = w' i) :
-- imply
  ∀ e ∈ prefixSet (σ : Fin n → E) k, codeMap μ (σ : Fin n → E) w e = codeMap μ (σ : Fin n → E) w' e := by
-- proof
  apply StatMech.OSSS.AdaptMConditional.codeMap_agree_on_prefix μ σ w w' k hagree

/--
[f_adapt_zero_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptMConditional.lean)
-/
@[path]
private lemma f_adapt_zero_eq_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {U V : Fin n → ℝ} :
-- imply
  f (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) 0)) = f (codeMap μ (σ : Fin n → E) U) := by
-- proof
  apply StatMech.OSSS.AdaptMConditional.f_adapt_zero_eq σ U V

/--
[adapt_step_eq_of_gt_stop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptMConditional.lean)
-/
@[path]
private lemma adapt_step_eq_of_gt_stop_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {U V : Fin n → ℝ}
  {t : ℕ}
-- given
  (ht : stopVal μ σ f U < t) :
-- imply
  codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) t) = codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) (t - 1)) := by
-- proof
  apply StatMech.OSSS.AdaptMConditional.adapt_step_eq_of_gt_stop σ U V t ht

/--
[measurable_stopVal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptMConditional.lean)
-/
@[path]
private lemma measurable_stopVal_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ} :
-- imply
  Measurable (fun U : Fin n → ℝ => stopVal μ σ f U) := by
-- proof
  apply StatMech.OSSS.AdaptMConditional.measurable_stopVal μ σ f

/--
[measurable_mixUV](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptMConditional.lean)
-/
@[path]
private lemma measurable_mixUV_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {m : ℕ} :
-- imply
  Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => mixUV p.1 p.2 m) := by
-- proof
  apply StatMech.OSSS.AdaptMConditional.measurable_mixUV m

/--
[measurable_adaptWt_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptMConditional.lean)
-/
@[path]
private lemma measurable_adaptWt_fixed_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {m s : ℕ} :
-- imply
  Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => adaptWt p.1 p.2 m s) := by
-- proof
  apply StatMech.OSSS.AdaptMConditional.measurable_adaptWt_fixed m s

/--
[measurable_g_adaptWt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptMConditional.lean)
-/
@[path]
private lemma measurable_g_adaptWt_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {g : ConfigSpace E → ℝ}
  {s : ℕ} :
-- imply
  Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => g (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) s))) := by
-- proof
  apply StatMech.OSSS.AdaptMConditional.measurable_g_adaptWt μ σ f g s

/--
[var_le_adapt_first_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptMConditional.lean)
-/
@[path]
private lemma var_le_adapt_first_step_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hf0 : 0 ≤ f)
  (hf1 : ∀ ω, f ω ≤ 1) :
-- imply
  Lindeberg.var μ f ≤ (1/2) * ∫ p, |f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) 0)) - f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) n))| ∂((Vcube n).prod (Vcube n)) := by
-- proof
  apply StatMech.OSSS.AdaptMConditional.var_le_adapt_first_step hpos hμ1 σ hf0 hf1

/--
[truncInd_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptMConditional.lean)
-/
@[path]
private lemma truncInd_le_one_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {U : Fin n → ℝ}
  {t : ℕ} :
-- imply
  |truncInd μ σ f U t| ≤ 1 := by
-- proof
  apply StatMech.OSSS.AdaptMConditional.truncInd_le_one μ σ f U t

/--
[measurable_truncInd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptMConditional.lean)
-/
@[path]
private lemma measurable_truncInd_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {t : ℕ} :
-- imply
  Measurable (fun U : Fin n → ℝ => truncInd μ σ f U t) := by
-- proof
  apply StatMech.OSSS.AdaptMConditional.measurable_truncInd μ σ f t

/--
[abs_adapt_step_eq_mul_truncInd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptMConditional.lean)
-/
@[path]
private lemma abs_adapt_step_eq_mul_truncInd_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {U V : Fin n → ℝ}
  {t : ℕ} :
-- imply
  |f (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) (t + 1))) - f (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) t))| = |f (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) (t + 1))) - f (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) t))| * truncInd μ σ f U (t + 1) := by
-- proof
  apply StatMech.OSSS.AdaptMConditional.abs_adapt_step_eq_mul_truncInd σ U V t

/--
[integrable_abs_adapt_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptMConditional.lean)
-/
@[path]
private lemma integrable_abs_adapt_step_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {Cf : ℝ}
  {s₁ s₂ : ℕ}
-- given
  (hfC : ∀ ω, |f ω| ≤ Cf) :
-- imply
  Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => |f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) s₁)) - f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) s₂))|) ((Vcube n).prod (Vcube n)) := by
-- proof
  apply StatMech.OSSS.AdaptMConditional.integrable_abs_adapt_step μ σ hfC s₁ s₂

/--
[integrable_abs_adapt_step_trunc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptMConditional.lean)
-/
@[path]
private lemma integrable_abs_adapt_step_trunc_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {Cf : ℝ}
  {t : ℕ}
-- given
  (hfC : ∀ ω, |f ω| ≤ Cf) :
-- imply
  Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => |f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) (t+1))) - f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) t))| * truncInd μ σ f p.1 (t + 1)) ((Vcube n).prod (Vcube n)) := by
-- proof
  apply StatMech.OSSS.AdaptMConditional.integrable_abs_adapt_step_trunc μ σ hfC t

/--
[trunc_telescope](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptMConditional.lean)
-/
@[path]
private lemma trunc_telescope_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {Cf : ℝ}
-- given
  (hfC : ∀ ω, |f ω| ≤ Cf) :
-- imply
  (∫ p, |f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) 0)) - f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) n))| ∂((Vcube n).prod (Vcube n))) ≤ ∑ t ∈ Finset.range n, ∫ p, |f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) (t+1))) - f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) t))| * truncInd μ σ f p.1 (t + 1) ∂((Vcube n).prod (Vcube n)) := by
-- proof
  apply StatMech.OSSS.AdaptMConditional.trunc_telescope σ hfC

/--
[var_le_trunc_telescope](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptMConditional.lean)
-/
@[path]
private lemma var_le_trunc_telescope_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hf0 : 0 ≤ f)
  (hf1 : ∀ ω, f ω ≤ 1) :
-- imply
  Lindeberg.var μ f ≤ (1/2) * ∑ t ∈ Finset.range n, ∫ p, |f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) (t+1))) - f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) t))| * truncInd μ σ f p.1 (t + 1) ∂((Vcube n).prod (Vcube n)) := by
-- proof
  apply StatMech.OSSS.AdaptMConditional.var_le_trunc_telescope hpos hμ1 σ hf0 hf1

/--
[integrable_truncInd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptMConditional.lean)
-/
@[path]
private lemma integrable_truncInd_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {t : ℕ} :
-- imply
  Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => truncInd μ σ f p.1 t) ((Vcube n).prod (Vcube n)) := by
-- proof
  apply StatMech.OSSS.AdaptMConditional.integrable_truncInd μ σ f t

/--
[integral_truncInd_eq_reveal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptMConditional.lean)
-/
@[path]
private lemma integral_truncInd_eq_reveal_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {i : Fin n} :
-- imply
  (∫ p, truncInd μ σ f p.1 ((i : ℕ) + 1) ∂((Vcube n).prod (Vcube n))) = revealAdapt μ σ f ((σ : Fin n → E) i) := by
-- proof
  apply StatMech.OSSS.AdaptMConditional.integral_truncInd_eq_reveal μ σ f i

/--
[tree_osss_sharp_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptMConditional.lean)
-/
@[path]
private lemma tree_osss_sharp_unconditional_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hf0 : 0 ≤ f)
  (hf1 : ∀ ω, f ω ≤ 1)
  (hStep : AdaptStepCovBound μ σ f) :
-- imply
  Lindeberg.var μ f ≤ ∑ e, revealAdapt μ σ f e * Lindeberg.cov μ f (Lindeberg.coord e) := by
-- proof
  apply StatMech.OSSS.AdaptMConditional.tree_osss_sharp_unconditional hpos hμ1 σ hf0 hf1 hStep

/--
[fk_q2_osss_sharp_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptMConditional.lean)
-/
@[path]
private lemma fk_q2_osss_sharp_unconditional_eq
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
  (hf0 : 0 ≤ f)
  (hf1 : ∀ ω, f ω ≤ 1)
  (hStep : AdaptStepCovBound (fkMass G p 2) σ f) :
-- imply
  Lindeberg.var (fkMass G p 2) f ≤ ∑ e, revealAdapt (fkMass G p 2) σ f e * Lindeberg.cov (fkMass G p 2) f (Lindeberg.coord e) := by
-- proof
  apply StatMech.OSSS.AdaptMConditional.fk_q2_osss_sharp_unconditional G hp hp1 σ hf0 hf1 hStep


-- created on 2026-10-23
