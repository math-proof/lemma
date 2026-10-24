import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.OSSS.UBlockFactor
open Finset MeasureTheory StatMech StatMech.OSSS StatMech.OSSS.AdaptDisintegration


/--
[ubfSplit_apply_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/UBlockFactor.lean)
-/
@[path]
private lemma ubfSplit_apply_fst_eq
  {n t : ℕ}
  {U : Fin n → ℝ}
-- given
  (i : {i : Fin n // (i : ℕ) < t}) :
-- imply
  ((ubfSplit n t) U).1 i = U (i : Fin n) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.ubfSplit_apply_fst n t U i

/--
[ubfSplit_apply_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/UBlockFactor.lean)
-/
@[path]
private lemma ubfSplit_apply_snd_eq
  {n t : ℕ}
  {U : Fin n → ℝ}
-- given
  (i : {i : Fin n // ¬ (i : ℕ) < t}) :
-- imply
  ((ubfSplit n t) U).2 i = U (i : Fin n) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.ubfSplit_apply_snd n t U i

/--
[ubf_pi_block_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/UBlockFactor.lean)
-/
@[path]
private lemma ubf_pi_block_split_eq
  {n t : ℕ} :
-- imply
  MeasurePreserving (ubfSplit n t) (cube n) ((ubfHead n t).prod (ubfTail n t)) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.ubf_pi_block_split n t

/--
[ubf_integrable_of_bdd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/UBlockFactor.lean)
-/
@[path]
private lemma ubf_integrable_of_bdd_eq
  {n : ℕ}
  {F : (Fin n → ℝ) → ℝ}
  {C : ℝ}
-- given
  (hF : Measurable F)
  (hC : ∀ U, |F U| ≤ C) :
-- imply
  Integrable F (cube n) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.ubf_integrable_of_bdd hF hC

/--
[ubf_integral_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/UBlockFactor.lean)
-/
@[path]
private lemma ubf_integral_factor_eq
  {n t : ℕ}
  {h₀ : ({i : Fin n // (i : ℕ) < t} → ℝ) → ℝ}
  {Ch : ℝ}
  {F : (Fin n → ℝ) → ℝ}
  {CF : ℝ}
-- given
  (hh₀m : Measurable h₀)
  (hh₀C : ∀ A, |h₀ A| ≤ Ch)
  (hFm : Measurable F)
  (hFC : ∀ U, |F U| ≤ CF) :
-- imply
  (∫ U, h₀ (((ubfSplit n t) U).1) * F U ∂(cube n)) = ∫ A, h₀ A * (∫ B, F ((ubfSplit n t).symm (A, B)) ∂(ubfTail n t)) ∂(ubfHead n t) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.ubf_integral_factor n t hh₀m hh₀C hFm hFC

/--
[ubf_integral_factor_of_factors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/UBlockFactor.lean)
-/
@[path]
private lemma ubf_integral_factor_of_factors_eq
  {n t : ℕ}
  {h : (Fin n → ℝ) → ℝ}
  {h₀ : ({i : Fin n // (i : ℕ) < t} → ℝ) → ℝ}
  {Ch : ℝ}
  {F : (Fin n → ℝ) → ℝ}
  {CF : ℝ}
-- given
  (hfac : ∀ U, h U = h₀ (((ubfSplit n t) U).1))
  (hh₀m : Measurable h₀)
  (hh₀C : ∀ A, |h₀ A| ≤ Ch)
  (hFm : Measurable F)
  (hFC : ∀ U, |F U| ≤ CF) :
-- imply
  (∫ U, h U * F U ∂(cube n)) = ∫ A, h₀ A * (∫ B, F ((ubfSplit n t).symm (A, B)) ∂(ubfTail n t)) ∂(ubfHead n t) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.ubf_integral_factor_of_factors n t hfac hh₀m hh₀C hFm hFC


-- created on 2026-10-23
