import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.StatisticalMechanics.Code.OSSS.AdaptCondBBProof2.Part2
open Finset MeasureTheory StatMech StatMech.OSSS StatMech.OSSS.AdaptDisintegration


/--
[acp_detAtC_congr_of_codeMap_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptCondBBProof2.lean)
-/
@[path]
private lemma acp_detAtC_congr_of_codeMap_agree_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {σ : Fin n → E}
  {f : ConfigSpace E → ℝ}
  {X X' : ConfigSpace E}
  {m : ℕ}
-- given
  (hpref : ∀ e ∈ prefixSet σ m, X e = X' e) :
-- imply
  detAtC σ f X m ↔ detAtC σ f X' m := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.acp_detAtC_congr_of_codeMap_agree σ f X X' m hpref

/--
[acp_stopVal_gt_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptCondBBProof2.lean)
-/
@[path]
private lemma acp_stopVal_gt_congr_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {U U' : Fin n → ℝ}
  {t : ℕ}
-- given
  (hagree : ∀ i : Fin n, (i : ℕ) < t → U i = U' i) :
-- imply
  (t + 1 ≤ stopVal μ σ f U) ↔ (t + 1 ≤ stopVal μ σ f U') := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.acp_stopVal_gt_congr μ σ f U U' t hagree

/--
[acp_truncInd_factors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptCondBBProof2.lean)
-/
@[path]
private lemma acp_truncInd_factors_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {t : ℕ}
  {U : Fin n → ℝ} :
-- imply
  truncInd μ σ f U (t + 1) = acp_truncHead μ σ f t (((ubfSplit n t) U).1) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.acp_truncInd_factors μ σ f t U

/--
[acp_measurable_truncHead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptCondBBProof2.lean)
-/
@[path]
private lemma acp_measurable_truncHead_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {t : ℕ} :
-- imply
  Measurable (acp_truncHead μ σ f t) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.acp_measurable_truncHead μ σ f t

/--
[acp_truncHead_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptCondBBProof2.lean)
-/
@[path]
private lemma acp_truncHead_le_one_eq
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
  |acp_truncHead μ σ f t A| ≤ 1 := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.acp_truncHead_le_one μ σ f t A

/--
[acp_measurable_fiberDiag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptCondBBProof2.lean)
-/
@[path]
private lemma acp_measurable_fiberDiag_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {e : E}
  {s : ℕ} :
-- imply
  Measurable (fun U : Fin n → ℝ => fiberDiag μ σ f e s U) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.acp_measurable_fiberDiag μ σ e s

/--
[acp_fiberDiag_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptCondBBProof2.lean)
-/
@[path]
private lemma acp_fiberDiag_le_one_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {e : E}
  {s : ℕ}
  {U : Fin n → ℝ}
-- given
  (hfC : ∀ ω, |f ω| ≤ 1) :
-- imply
  |fiberDiag μ σ f e s U| ≤ 1 := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.acp_fiberDiag_le_one μ σ hfC e s U

/--
[acp_measurable_fiberCross_marg_f](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptCondBBProof2.lean)
-/
@[path]
private lemma acp_measurable_fiberCross_marg_f_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {s : ℕ} :
-- imply
  Measurable (fun U : Fin n → ℝ => ∫ V, f (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) s)) ∂(Vcube n)) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.acp_measurable_fiberCross_marg_f μ σ s

/--
[acp_measurable_fiberCross_marg_c](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptCondBBProof2.lean)
-/
@[path]
private lemma acp_measurable_fiberCross_marg_c_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {e : E}
  {s : ℕ} :
-- imply
  Measurable (fun U : Fin n → ℝ => ∫ V, Lindeberg.coord e (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) s)) ∂(Vcube n)) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.acp_measurable_fiberCross_marg_c μ σ e s

/--
[acp_measurable_fiberCross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptCondBBProof2.lean)
-/
@[path]
private lemma acp_measurable_fiberCross_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {e : E}
  {s₁ s₂ : ℕ} :
-- imply
  Measurable (fun U : Fin n → ℝ => fiberCross μ σ f e s₁ s₂ U) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.acp_measurable_fiberCross μ σ e s₁ s₂

/--
[acp_fiberCross_marg_f_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptCondBBProof2.lean)
-/
@[path]
private lemma acp_fiberCross_marg_f_le_one_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {s : ℕ}
  {U : Fin n → ℝ}
-- given
  (hfC : ∀ ω, |f ω| ≤ 1) :
-- imply
  |∫ V, f (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) s)) ∂(Vcube n)| ≤ 1 := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.acp_fiberCross_marg_f_le_one μ σ hfC s U

/--
[acp_fiberCross_marg_c_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptCondBBProof2.lean)
-/
@[path]
private lemma acp_fiberCross_marg_c_le_one_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {e : E}
  {s : ℕ}
  {U : Fin n → ℝ} :
-- imply
  |∫ V, Lindeberg.coord e (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) s)) ∂(Vcube n)| ≤ 1 := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.acp_fiberCross_marg_c_le_one μ σ e s U

/--
[acp_fiberCross_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptCondBBProof2.lean)
-/
@[path]
private lemma acp_fiberCross_le_one_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {e : E}
  {s₁ s₂ : ℕ}
  {U : Fin n → ℝ}
-- given
  (hfC : ∀ ω, |f ω| ≤ 1) :
-- imply
  |fiberCross μ σ f e s₁ s₂ U| ≤ 1 := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.acp_fiberCross_le_one μ σ hfC e s₁ s₂ U


-- created on 2026-10-23
