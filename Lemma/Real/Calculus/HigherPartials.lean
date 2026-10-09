import Mathlib
import sympy.Basic
import sympy.Analysis.Calculus.HigherPartials

open Real.Calculus.HigherPartials

/--
[partialDeriv_spec](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Calculus/HigherPartials.lean)
-/
@[path]
private lemma partialDeriv_spec_eq
-- given
  {n : ℕ} (f : (Fin n → ℝ) → ℝ) (i : Fin n) (x : Fin n → ℝ) :
-- imply
  partialDeriv f i x =
    deriv (fun t : ℝ => f (x + t • Pi.single i (1 : ℝ))) 0 := by
-- proof
  apply partialDeriv_spec f i x


/--
[partialDeriv_eq_fderiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Calculus/HigherPartials.lean)
-/
@[path]
private lemma partialDeriv_eq_fderiv_apply_eq
-- given
  {n : ℕ} (f : (Fin n → ℝ) → ℝ) (i : Fin n) (x : Fin n → ℝ)
  (hf : DifferentiableAt ℝ f x) :
-- imply
  partialDeriv f i x = fderiv ℝ f x (Pi.single i (1 : ℝ)) := by
-- proof
  apply partialDeriv_eq_fderiv_apply f i x hf


/--
[partialDeriv_eq_fderiv_apply_of_differentiable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Calculus/HigherPartials.lean)
-/
@[path]
private lemma partialDeriv_eq_fderiv_apply_of_differentiable_eq
-- given
  {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : Differentiable ℝ f) (i : Fin n) :
-- imply
  partialDeriv f i = fun x => fderiv ℝ f x (Pi.single i (1 : ℝ)) := by
-- proof
  apply partialDeriv_eq_fderiv_apply_of_differentiable f i hf


/--
[partialDeriv_partialDeriv_eq_fderiv_fderiv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Calculus/HigherPartials.lean)
-/
@[path]
private lemma partialDeriv_partialDeriv_eq_fderiv_fderiv_eq
-- given
  {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ 2 f) (i j : Fin n) (x : Fin n → ℝ) :
-- imply
  partialDeriv (partialDeriv f i) j x =
    fderiv ℝ (fderiv ℝ f) x (Pi.single j (1 : ℝ)) (Pi.single i (1 : ℝ)) := by
-- proof
  apply partialDeriv_partialDeriv_eq_fderiv_fderiv f i j x hf


/--
[iterated_partialDeriv_commute](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Calculus/HigherPartials.lean)
-/
@[path]
private lemma iterated_partialDeriv_commute_eq
-- given
  {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ 2 f) (i j : Fin n) (x : Fin n → ℝ) :
-- imply
  partialDeriv (partialDeriv f i) j x =
    partialDeriv (partialDeriv f j) i x := by
-- proof
  apply iterated_partialDeriv_commute f i j x hf


-- created on 2026-10-09
