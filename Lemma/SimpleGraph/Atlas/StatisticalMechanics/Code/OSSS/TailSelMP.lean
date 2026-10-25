import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.OSSS.TailSelMP.Part3
open Finset MeasureTheory StatMech StatMech.OSSS StatMech.OSSS.AdaptDisintegration


/--
[tsm_map_restrict_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailSelMP.lean)
-/
@[path]
private lemma tsm_map_restrict_congr_eq
  [Fintype E]
  [DecidableEq E]
  [MeasurableSpace α]
  [MeasurableSpace β]
  {μ : Measure α}
  {S : Set α}
  {h h' : α → β}
-- given
  (hh : Measurable h)
  (hh' : Measurable h')
  (hagree : ∀ x ∈ S, h x = h' x) :
-- imply
  Measure.map h (μ.restrict S) = Measure.map h' (μ.restrict S) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.tsm_map_restrict_congr μ S hh hh' hagree

/--
[tsm_measurePreserving_of_partition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailSelMP.lean)
-/
@[path]
private lemma tsm_measurePreserving_of_partition_eq
  [Fintype E]
  [DecidableEq E]
  [MeasurableSpace α]
  [MeasurableSpace β]
  {μ : Measure α}
  {ν : Measure β}
  {S : ℕ → Set α}
  {h : α → β}
  {hk : ℕ → α → β}
-- given
  (hSmeas : ∀ k, MeasurableSet (S k))
  (hSdisj : Pairwise (Function.onFun Disjoint S))
  (hScover : ⋃ k, S k = Set.univ)
  (hh : Measurable h)
  (hhk : ∀ k, Measurable (hk k))
  (hagree : ∀ k, ∀ x ∈ S k, h x = hk k x)
  (hsum : (Measure.sum (fun k => Measure.map (hk k) (μ.restrict (S k)))) = ν) :
-- imply
  MeasurePreserving h μ ν := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.tsm_measurePreserving_of_partition hSmeas hSdisj hScover hh hhk hagree hsum

/--
[tsm_measurable_selRand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailSelMP.lean)
-/
@[path]
private lemma tsm_measurable_selRand_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {t s : ℕ}
-- given
  (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
-- imply
  Measurable (atl_selRand μ σ f t s A) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.tsm_measurable_selRand μ σ f t s A

/--
[tsm_measurable_switch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailSelMP.lean)
-/
@[path]
private lemma tsm_measurable_switch_eq
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
  Measurable (fun p : ({i : Fin n // ¬ (i : ℕ) < t} → ℝ) × (Fin n → ℝ) => stopVal μ σ f (acp_join t A p.1)) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.tsm_measurable_switch μ σ f t A

/--
[tsm_switchPiece_meas](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailSelMP.lean)
-/
@[path]
private lemma tsm_switchPiece_meas_eq
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
  MeasurableSet (tsm_switchPiece μ σ f t A k) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.tsm_switchPiece_meas μ σ f t A k

/--
[tsm_switchPiece_disj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailSelMP.lean)
-/
@[path]
private lemma tsm_switchPiece_disj_eq
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
  Pairwise (Function.onFun Disjoint (tsm_switchPiece μ σ f t A)) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.tsm_switchPiece_disj μ σ f t A

/--
[tsm_switchPiece_cover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailSelMP.lean)
-/
@[path]
private lemma tsm_switchPiece_cover_eq
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
  ⋃ k, tsm_switchPiece μ σ f t A k = Set.univ := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.tsm_switchPiece_cover μ σ f t A

/--
[tsm_selRand_eq_on_piece](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailSelMP.lean)
-/
@[path]
private lemma tsm_selRand_eq_on_piece_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {t s : ℕ}
  {k : ℕ}
-- given
  (A : {i : Fin n // (i : ℕ) < t} → ℝ)
  (p : ({i : Fin n // ¬ (i : ℕ) < t} → ℝ) × (Fin n → ℝ))
  (hp : p ∈ tsm_switchPiece μ σ f t A k) :
-- imply
  atl_selRand μ σ f t s A p = osp_tailSelFixed t s k A p := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.tsm_selRand_eq_on_piece μ σ f t s A k p hp

/--
[tsm_tailSelMP_of_restrictedSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailSelMP.lean)
-/
@[path]
private lemma tsm_tailSelMP_of_restrictedSum_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {t s : ℕ}
-- given
  (A : {i : Fin n // (i : ℕ) < t} → ℝ)
  (hres : tsm_TailSelMP_restrictedSum μ σ f t s A) :
-- imply
  atl_TailSelMP μ σ f t s A := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.tsm_tailSelMP_of_restrictedSum μ σ f t s A hres

/--
[tsm_switchPiece_const_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailSelMP.lean)
-/
@[path]
private lemma tsm_switchPiece_const_eq_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {t : ℕ}
  {k₀ : ℕ}
-- given
  (A : {i : Fin n // (i : ℕ) < t} → ℝ)
  (hconst : ∀ B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ, stopVal μ σ f (acp_join t A B) = k₀) :
-- imply
  tsm_switchPiece μ σ f t A k₀ = Set.univ := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.tsm_switchPiece_const_eq μ σ t A k₀ hconst

/--
[tsm_switchPiece_const_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailSelMP.lean)
-/
@[path]
private lemma tsm_switchPiece_const_empty_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {t : ℕ}
  {k₀ : ℕ}
  {k : ℕ}
-- given
  (A : {i : Fin n // (i : ℕ) < t} → ℝ)
  (hconst : ∀ B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ, stopVal μ σ f (acp_join t A B) = k₀)
  (hk : k ≠ k₀) :
-- imply
  tsm_switchPiece μ σ f t A k = ∅ := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.tsm_switchPiece_const_empty μ σ t A k₀ hconst k hk

/--
[tsm_restrictedSum_of_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailSelMP.lean)
-/
@[path]
private lemma tsm_restrictedSum_of_const_eq
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
  tsm_TailSelMP_restrictedSum μ σ f t s A := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.tsm_restrictedSum_of_const μ σ t s hts A k₀ hconst

/--
[tsm_tailSelMP_of_const_switch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailSelMP.lean)
-/
@[path]
private lemma tsm_tailSelMP_of_const_switch_eq
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
  apply StatMech.OSSS.AdaptDisintegration.tsm_tailSelMP_of_const_switch μ σ t s hts A k₀ hconst


-- created on 2026-10-23
