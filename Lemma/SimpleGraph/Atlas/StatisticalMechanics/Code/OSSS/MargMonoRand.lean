import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.OSSS.MargMonoRand
open Finset MeasureTheory StatMech StatMech.OSSS StatMech.OSSS.AdaptDisintegration


/--
[mmr_join_mono_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/MargMonoRand.lean)
-/
@[path]
private lemma mmr_join_mono_tail_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {t : ℕ}
  {B B' : {i : Fin n // ¬ (i : ℕ) < t} → ℝ}
-- given
  (A : {i : Fin n // (i : ℕ) < t} → ℝ)
  (hBB : B ≤ B') :
-- imply
  acp_join t A B ≤ acp_join t A B' := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.mmr_join_mono_tail t A hBB

/--
[mmr_margRand_eq_of_stop_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/MargMonoRand.lean)
-/
@[path]
private lemma mmr_margRand_eq_of_stop_le_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f g : ConfigSpace E → ℝ}
  {t s : ℕ}
-- given
  (A : {i : Fin n // (i : ℕ) < t} → ℝ)
  (hstop : ∀ B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ, stopVal μ σ f (acp_join t A B) ≤ s) :
-- imply
  atl_margRand μ σ f g t s A = (fun _ : {i : Fin n // ¬ (i : ℕ) < t} → ℝ => ∫ V, g (codeMap μ (σ : Fin n → E) V) ∂(Vcube n)) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.mmr_margRand_eq_of_stop_le μ σ f g t s A hstop

/--
[mmr_margMonoRand_of_stop_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/MargMonoRand.lean)
-/
@[path]
private lemma mmr_margMonoRand_of_stop_le_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f g : ConfigSpace E → ℝ}
  {t s : ℕ}
-- given
  (A : {i : Fin n // (i : ℕ) < t} → ℝ)
  (hstop : ∀ B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ, stopVal μ σ f (acp_join t A B) ≤ s) :
-- imply
  atl_MargMonoRand μ σ f g t s A := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.mmr_margMonoRand_of_stop_le μ σ f g t s A hstop

/--
[mmr_margMonoRand_at_n](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/MargMonoRand.lean)
-/
@[path]
private lemma mmr_margMonoRand_at_n_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f g : ConfigSpace E → ℝ}
  {t : ℕ}
-- given
  (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
-- imply
  atl_MargMonoRand μ σ f g t n A := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.mmr_margMonoRand_at_n μ σ f g t A

/--
[mmr_margRand_f_at_zero_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/MargMonoRand.lean)
-/
@[path]
private lemma mmr_margRand_f_at_zero_eq_eq
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
  atl_margRand μ σ f f t 0 A = (fun B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ => f (codeMap μ (σ : Fin n → E) (acp_join t A B))) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.mmr_margRand_f_at_zero_eq μ σ f t A

/--
[mmr_margMonoRand_f_at_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/MargMonoRand.lean)
-/
@[path]
private lemma mmr_margMonoRand_f_at_zero_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {t : ℕ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hmono : IsMonotonicMeasure μ)
  (hf : Monotone f)
  (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
-- imply
  atl_MargMonoRand μ σ f f t 0 A := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.mmr_margMonoRand_f_at_zero hpos hmono σ hf t A

/--
[mmr_margMonoRand_of_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/MargMonoRand.lean)
-/
@[path]
private lemma mmr_margMonoRand_of_const_eq
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
  apply StatMech.OSSS.AdaptDisintegration.mmr_margMonoRand_of_const hpos hmono σ hg hgC t s A m₀ hconst


-- created on 2026-10-23
