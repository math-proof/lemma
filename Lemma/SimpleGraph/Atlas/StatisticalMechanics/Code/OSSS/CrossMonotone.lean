import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.OSSS.CrossMonotone
open Finset MeasureTheory StatMech StatMech.OSSS StatMech.OSSS.AdaptDisintegration


/--
[cmn_detAtC_prefix_local](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/CrossMonotone.lean)
-/
@[path]
private lemma cmn_detAtC_prefix_local_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {σ : Fin n → E}
  {f : ConfigSpace E → ℝ}
  {X X' : ConfigSpace E}
  {t : ℕ}
-- given
  (hagree : ∀ e ∈ prefixSet σ t, X e = X' e) :
-- imply
  detAtC σ f X t ↔ detAtC σ f X' t := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.cmn_detAtC_prefix_local σ f X X' t hagree

/--
[cmn_detAtC_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/CrossMonotone.lean)
-/
@[path]
private lemma cmn_detAtC_mono_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {σ : Fin n → E}
  {f : ConfigSpace E → ℝ}
  {X : ConfigSpace E}
  {j k : ℕ}
-- given
  (hjk : j ≤ k)
  (hdet : detAtC σ f X j) :
-- imply
  detAtC σ f X k := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.cmn_detAtC_mono σ f X hjk hdet

/--
[cmn_stopValC_le_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/CrossMonotone.lean)
-/
@[path]
private lemma cmn_stopValC_le_iff_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {X : ConfigSpace E}
  {t : ℕ} :
-- imply
  stopValC σ f X ≤ t ↔ detAtC (σ : Fin n → E) f X t := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.cmn_stopValC_le_iff σ f X t

/--
[cmn_stop_lt_const_in_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/CrossMonotone.lean)
-/
@[path]
private lemma cmn_stop_lt_const_in_tail_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {t : ℕ}
-- given
  (A : {i : Fin n // (i : ℕ) < t} → ℝ)
  (B B' : {i : Fin n // ¬ (i : ℕ) < t} → ℝ) :
-- imply
  (t < stopVal μ σ f (acp_join t A B)) ↔ (t < stopVal μ σ f (acp_join t A B')) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.cmn_stop_lt_const_in_tail μ σ f t A B B'

/--
[cmn_coord_bit_local](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/CrossMonotone.lean)
-/
@[path]
private lemma cmn_coord_bit_local_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {t : ℕ}
  {V : Fin n → ℝ}
-- given
  (htn : t < n)
  (A : {i : Fin n // (i : ℕ) < t} → ℝ)
  (B B' : {i : Fin n // ¬ (i : ℕ) < t} → ℝ)
  (hbt : B ⟨⟨t, htn⟩, by simp⟩ = B' ⟨⟨t, htn⟩, by simp⟩) :
-- imply
  codeMap μ (σ : Fin n → E) (adaptWt (acp_join t A B) V (stopVal μ σ f (acp_join t A B)) t) ((σ : Fin n → E) ⟨t, htn⟩) = codeMap μ (σ : Fin n → E) (adaptWt (acp_join t A B') V (stopVal μ σ f (acp_join t A B')) t) ((σ : Fin n → E) ⟨t, htn⟩) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.cmn_coord_bit_local μ σ f t htn A B B' hbt V

/--
[cmn_M2_local](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/CrossMonotone.lean)
-/
@[path]
private lemma cmn_M2_local_eq
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
  (B B' : {i : Fin n // ¬ (i : ℕ) < t} → ℝ)
  (hbt : B ⟨⟨t, htn⟩, by simp⟩ = B' ⟨⟨t, htn⟩, by simp⟩) :
-- imply
  atl_margRand μ σ f (Lindeberg.coord ((σ : Fin n → E) ⟨t, htn⟩)) t t A B = atl_margRand μ σ f (Lindeberg.coord ((σ : Fin n → E) ⟨t, htn⟩)) t t A B' := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.cmn_M2_local μ σ f t htn A B B' hbt

/--
[cmn_disint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/CrossMonotone.lean)
-/
@[path]
private lemma cmn_disint_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {t : ℕ}
  {h : ({i : Fin n // ¬ (i : ℕ) < t} → ℝ) → ℝ}
  {C : ℝ}
-- given
  (hmeas : Measurable h)
  (hbdd : ∀ B, |h B| ≤ C) :
-- imply
  (∫ B, h B ∂(ubfTail n t)) = ∫ c, (∫ B', h ((sp1_tailDisint n t).symm (B', c)) ∂(ubfTail n (t+1))) ∂(Measure.pi (fun _ : sp1_Sing n t => unitMeasure)) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.cmn_disint t hmeas hbdd

/--
[cmn_symm_coord_t](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/CrossMonotone.lean)
-/
@[path]
private lemma cmn_symm_coord_t_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {t : ℕ}
  {c : sp1_Sing n t → ℝ}
-- given
  (htn : t < n)
  (B' : {i : Fin n // ¬ (i : ℕ) < t+1} → ℝ) :
-- imply
  (sp1_tailDisint n t).symm (B', c) ⟨⟨t, htn⟩, by simp⟩ = c ⟨⟨⟨t, htn⟩, by simp⟩, by simp⟩ := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.cmn_symm_coord_t t htn B' c

/--
[cmn_join_reassemble](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/CrossMonotone.lean)
-/
@[path]
private lemma cmn_join_reassemble_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {t : ℕ}
  {c : sp1_Sing n t → ℝ}
-- given
  (htn : t < n)
  (A : {i : Fin n // (i : ℕ) < t} → ℝ)
  (B' : {i : Fin n // ¬ (i : ℕ) < t+1} → ℝ) :
-- imply
  acp_join t A ((sp1_tailDisint n t).symm (B', c)) = acp_join (t+1) (sp1_headExtC t htn A c) B' := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.cmn_join_reassemble t htn A B' c

/--
[cmn_M1_reassemble](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/CrossMonotone.lean)
-/
@[path]
private lemma cmn_M1_reassemble_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {t : ℕ}
  {c : sp1_Sing n t → ℝ}
-- given
  (htn : t < n)
  (A : {i : Fin n // (i : ℕ) < t} → ℝ)
  (B' : {i : Fin n // ¬ (i : ℕ) < t+1} → ℝ) :
-- imply
  atl_margRand μ σ f f t (t+1) A ((sp1_tailDisint n t).symm (B', c)) = atl_margRand μ σ f f (t+1) (t+1) (sp1_headExtC t htn A c) B' := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.cmn_M1_reassemble μ σ f t htn A B' c

/--
[cmn_cross_pred_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/CrossMonotone.lean)
-/
@[path]
private lemma cmn_cross_pred_eq_eq
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
  (hmono : IsMonotonicMeasure μ)
  (hf : Monotone f)
  (hfC : ∀ ω, |f ω| ≤ 1)
  (htn : t < n)
  (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
-- imply
  (∫ B, fiberCross μ σ f ((σ : Fin n → E) ⟨t, htn⟩) (t+1) t (acp_join t A B) ∂(ubfTail n t)) = Lindeberg.mean μ f * Lindeberg.mean μ (Lindeberg.coord ((σ : Fin n → E) ⟨t, htn⟩)) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.cmn_cross_pred_eq μ hpos hμ1 hmono σ hf hfC t htn A

/--
[cmn_Cross41](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/CrossMonotone.lean)
-/
@[path]
private lemma cmn_Cross41_eq
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
  (hmono : IsMonotonicMeasure μ)
  (hf : Monotone f)
  (hfC : ∀ ω, |f ω| ≤ 1)
  (htn : t < n)
  (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
-- imply
  cvf_Cross41 μ σ f t htn A := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.cmn_Cross41 hpos hμ1 hmono σ hf hfC t htn A

/--
[cmn_tailCondLaw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/CrossMonotone.lean)
-/
@[path]
private lemma cmn_tailCondLaw_eq
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
  acp_TailCondLaw μ σ f := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.cmn_tailCondLaw hpos hμ1 hmono σ hf hfC


-- created on 2026-10-23
