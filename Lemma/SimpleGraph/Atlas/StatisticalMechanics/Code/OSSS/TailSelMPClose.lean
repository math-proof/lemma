import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.OSSS.TailSelMPClose
open Finset MeasureTheory StatMech StatMech.OSSS StatMech.OSSS.AdaptDisintegration


/--
[tsc_restrictedSum_of_recover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailSelMPClose.lean)
-/
@[path]
private lemma tsc_restrictedSum_of_recover_eq
  [Fintype E]
  [DecidableEq E]
  [MeasurableSpace α]
  [MeasurableSpace β]
  {μ : Measure α}
  {ν : Measure β}
  [IsProbabilityMeasure μ]
  [IsProbabilityMeasure ν]
  {S : ℕ → Set α}
  {Φ : ℕ → α → β}
  {R : β → ℕ}
-- given
  (hSmeas : ∀ k, MeasurableSet (S k))
  (hSdisj : Pairwise (Function.onFun Disjoint S))
  (hScover : ⋃ k, S k = Set.univ)
  (hΦmeas : ∀ k, Measurable (Φ k))
  (hRmeas : Measurable R)
  (hMP : ∀ k, MeasurePreserving (Φ k) μ ν)
  (hSsub : ∀ k, S k ⊆ Φ k ⁻¹' (R ⁻¹' {k})) :
-- imply
  (Measure.sum (fun k => Measure.map (Φ k) (μ.restrict (S k)))) = ν := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.tsc_restrictedSum_of_recover hSmeas hSdisj hScover hΦmeas hRmeas hMP hSsub

/--
[tsc_prefixSet_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailSelMPClose.lean)
-/
@[path]
private lemma tsc_prefixSet_mono_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {σ : Fin n → E}
  {j k : ℕ}
-- given
  (hjk : j ≤ k) :
-- imply
  prefixSet σ j ⊆ prefixSet σ k := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.tsc_prefixSet_mono σ hjk

/--
[tsc_detAtC_transport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailSelMPClose.lean)
-/
@[path]
private lemma tsc_detAtC_transport_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {σ : Fin n → E}
  {f : ConfigSpace E → ℝ}
  {X X' : ConfigSpace E}
  {k : ℕ}
  {j : ℕ}
-- given
  (hagree : ∀ e ∈ prefixSet σ k, X e = X' e)
  (hjk : j ≤ k)
  (hdet : detAtC σ f X j) :
-- imply
  detAtC σ f X' j := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.tsc_detAtC_transport σ f X X' k hagree j hjk hdet

/--
[tsc_stopValC_determinesC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailSelMPClose.lean)
-/
@[path]
private lemma tsc_stopValC_determinesC_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {X : ConfigSpace E} :
-- imply
  detAtC (σ : Fin n → E) f X (stopValC σ f X) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.tsc_stopValC_determinesC σ f X

/--
[tsc_stopValC_stable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailSelMPClose.lean)
-/
@[path]
private lemma tsc_stopValC_stable_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {X X' : ConfigSpace E}
  {k : ℕ}
-- given
  (hagree : ∀ e ∈ prefixSet (σ : Fin n → E) k, X e = X' e)
  (hk : stopValC σ f X = k) :
-- imply
  stopValC σ f X' = k := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.tsc_stopValC_stable σ f X X' k hagree hk

/--
[tsc_acp_join_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailSelMPClose.lean)
-/
@[path]
private lemma tsc_acp_join_head_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {t : ℕ}
  {i : Fin n}
-- given
  (A : {i : Fin n // (i : ℕ) < t} → ℝ)
  (B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ)
  (hi : (i : ℕ) < t) :
-- imply
  acp_join t A B i = A ⟨i, hi⟩ := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.tsc_acp_join_head t A B i hi

/--
[tsc_acp_join_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailSelMPClose.lean)
-/
@[path]
private lemma tsc_acp_join_tail_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {t : ℕ}
  {i : Fin n}
-- given
  (A : {i : Fin n // (i : ℕ) < t} → ℝ)
  (B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ)
  (hi : ¬ (i : ℕ) < t) :
-- imply
  acp_join t A B i = B ⟨i, hi⟩ := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.tsc_acp_join_tail t A B i hi

/--
[tsc_recover_meas](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailSelMPClose.lean)
-/
@[path]
private lemma tsc_recover_meas_eq
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
  Measurable (tsc_recover μ σ f t A) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.tsc_recover_meas μ σ f t A

/--
[tsc_recover_eq_of_piece](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailSelMPClose.lean)
-/
@[path]
private lemma tsc_recover_eq_of_piece_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {t k : ℕ}
-- given
  (A : {i : Fin n // (i : ℕ) < t} → ℝ)
  (p : ({i : Fin n // ¬ (i : ℕ) < t} → ℝ) × (Fin n → ℝ))
  (hp : stopVal μ σ f (acp_join t A p.1) = k) :
-- imply
  tsc_recover μ σ f t A (osp_tailSelFixed t t k A p) = k := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.tsc_recover_eq_of_piece μ σ f t k A p hp

/--
[tsc_piece_subset_recover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailSelMPClose.lean)
-/
@[path]
private lemma tsc_piece_subset_recover_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {t : ℕ}
  {k : ℕ}
-- given
  (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
-- imply
  tsm_switchPiece μ σ f t A k ⊆ (osp_tailSelFixed t t k A) ⁻¹' ((tsc_recover μ σ f t A) ⁻¹' {k}) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.tsc_piece_subset_recover μ σ f t A k

/--
[tsc_restrictedSum_at_s_eq_t](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailSelMPClose.lean)
-/
@[path]
private lemma tsc_restrictedSum_at_s_eq_t_eq
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
  tsm_TailSelMP_restrictedSum μ σ f t t A := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.tsc_restrictedSum_at_s_eq_t μ σ f t A

/--
[tsc_tailSelMP_at_s_eq_t](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailSelMPClose.lean)
-/
@[path]
private lemma tsc_tailSelMP_at_s_eq_t_eq
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
  atl_TailSelMP μ σ f t t A := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.tsc_tailSelMP_at_s_eq_t μ σ f t A


-- created on 2026-10-23
