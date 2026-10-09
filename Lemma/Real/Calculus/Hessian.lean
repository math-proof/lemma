import Mathlib
import sympy.Basic
import sympy.Analysis.Calculus.Hessian

open Real.Calculus.Hessian
open scoped BigOperators

/--
[hessianMatrix_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Calculus/Hessian.lean)
-/
@[path]
private lemma hessianMatrix_apply_eq
-- given
  {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) (i j : Fin n) :
-- imply
  hessianMatrix f x i j =
    deriv (fun s : ℝ => deriv (fun t : ℝ =>
      f (x + s • Pi.single i (1 : ℝ) + t • Pi.single j (1 : ℝ))) 0) 0 := by
-- proof
  apply hessianMatrix_apply f x i j


/--
[hessianMatrix_eq_fderiv_fderiv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Calculus/Hessian.lean)
-/
@[path]
private lemma hessianMatrix_eq_fderiv_fderiv_eq
-- given
  {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ 2 f) (x : Fin n → ℝ) (i j : Fin n) :
-- imply
  hessianMatrix f x i j =
    fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1) := by
-- proof
  apply hessianMatrix_eq_fderiv_fderiv f hf x i j


/--
[hessianMatrix_symmetric](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Calculus/Hessian.lean)
-/
@[path]
private lemma hessianMatrix_symmetric_eq
-- given
  {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ 2 f) (x : Fin n → ℝ) :
-- imply
  (hessianMatrix f x).transpose = hessianMatrix f x := by
-- proof
  apply hessianMatrix_symmetric f hf x


/--
[IsLocalMin.deriv_deriv_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Calculus/Hessian.lean)
-/
@[path]
private lemma isLocalMin_deriv_deriv_nonneg_eq
-- given
  {g : ℝ → ℝ} {x : ℝ} (hmin : IsLocalMin g x) (hg : ContDiff ℝ 2 g) :
-- imply
  0 ≤ deriv (deriv g) x := by
-- proof
  apply IsLocalMin.deriv_deriv_nonneg hmin hg


/--
[isLocalMin_hessian_quadratic_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Calculus/Hessian.lean)
-/
@[path]
private lemma isLocalMin_hessian_quadratic_nonneg_eq
-- given
  {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)
  (hf : ContDiff ℝ 2 f) (hmin : IsLocalMin f x) (v : Fin n → ℝ) :
-- imply
  0 ≤ ∑ i, ∑ j, v i * hessianMatrix f x i j * v j := by
-- proof
  apply isLocalMin_hessian_quadratic_nonneg f hf x hmin v


-- created on 2026-10-09
