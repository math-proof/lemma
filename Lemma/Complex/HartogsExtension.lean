import Mathlib
import sympy.Basic
import sympy.Analysis.Complex.HartogsExtension

open Complex.HartogsWanted

/--
[continuousOn_fderiv_of_differentiableOn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/HartogsExtension.lean)
-/
@[path]
private lemma continuousOn_fderiv_of_differentiableOn_eq
-- given
  {n : ℕ} {s : Set (EuclideanSpace ℂ (Fin n))}
  {f : EuclideanSpace ℂ (Fin n) → ℂ} (hs : IsOpen s)
  (hf : DifferentiableOn ℂ f s) :
-- imply
  ContinuousOn (fderiv ℂ f) s := by
-- proof
  apply continuousOn_fderiv_of_differentiableOn hs hf

/--
[barDeriv_eq_zero_of_differentiableAt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/HartogsExtension.lean)
-/
@[path]
private lemma barDeriv_eq_zero_of_differentiableAt_eq
-- given
  {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f z) :
-- imply
  barDeriv f z = 0 := by
-- proof
  apply barDeriv_eq_zero_of_differentiableAt hf

/--
[differentiableAt_of_barDeriv_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/HartogsExtension.lean)
-/
@[path]
private lemma differentiableAt_of_barDeriv_eq_zero_eq
-- given
  {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z)
  (hbar : barDeriv f z = 0) :
-- imply
  DifferentiableAt ℂ f z := by
-- proof
  apply differentiableAt_of_barDeriv_eq_zero hf hbar

/--
[exists_differentiable_barDeriv_eq_of_hasCompactSupport](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/HartogsExtension.lean)
-/
@[path]
private lemma exists_differentiable_barDeriv_eq_of_hasCompactSupport_eq
-- given
  {g : ℂ → ℂ} (hg : Differentiable ℝ g)
  (hDg : Continuous (fderiv ℝ g))
  (hgc : HasCompactSupport g) :
-- imply
  ∃ u : ℂ → ℂ, Differentiable ℝ u ∧ ∀ z, barDeriv u z = g z := by
-- proof
  apply exists_differentiable_barDeriv_eq_of_hasCompactSupport hg hDg hgc

/--
[hartogs_extension](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/HartogsExtension.lean)
-/
@[path]
private lemma hartogs_extension_eq
-- given
  {n : ℕ} {U K : Set (EuclideanSpace ℂ (Fin n))}
  {f : EuclideanSpace ℂ (Fin n) → ℂ}
  (hn : 2 ≤ n) (hU_open : IsOpen U) (hU_conn : IsConnected U)
  (hK_compact : IsCompact K) (hKU : K ⊆ U) (hUK_conn : IsConnected (U \ K))
  (hf : DifferentiableOn ℂ f (U \ K)) :
-- imply
  ∃ F : EuclideanSpace ℂ (Fin n) → ℂ, DifferentiableOn ℂ F U ∧ Set.EqOn F f (U \ K) := by
-- proof
  apply hartogs_extension hn hU_open hU_conn hK_compact hKU hUK_conn hf


-- created on 2026-10-09
