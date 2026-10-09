import Mathlib
import sympy.Basic
import sympy.Analysis.Calculus.Jacobian

open Real.Calculus.Jacobian
open scoped Matrix

/--
[jacobianMatrix_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Calculus/Jacobian.lean)
-/
@[path]
private lemma jacobianMatrix_apply_eq
-- given
  {m n : ℕ} (f : (Fin m → ℝ) → (Fin n → ℝ)) (x : Fin m → ℝ) (i : Fin n) (j : Fin m) :
-- imply
  jacobianMatrix f x i j =
    deriv (fun t : ℝ => f (x + t • Pi.single j (1 : ℝ)) i) 0 := by
-- proof
  apply jacobianMatrix_apply f x i j


/--
[jacobianMatrix_apply_of_differentiableAt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Calculus/Jacobian.lean)
-/
@[path]
private lemma jacobianMatrix_apply_of_differentiableAt_eq
-- given
  {m n : ℕ} (f : (Fin m → ℝ) → (Fin n → ℝ)) (x : Fin m → ℝ)
  (hf : DifferentiableAt ℝ f x) (i : Fin n) (j : Fin m) :
-- imply
  jacobianMatrix f x i j = fderiv ℝ f x (Pi.single j (1 : ℝ)) i := by
-- proof
  apply jacobianMatrix_apply_of_differentiableAt f x hf i j


/--
[jacobianMatrix_eq_toMatrix'_fderiv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Calculus/Jacobian.lean)
-/
@[path]
private lemma jacobianMatrix_eq_toMatrix'_fderiv_eq
-- given
  {m n : ℕ} (f : (Fin m → ℝ) → (Fin n → ℝ)) (x : Fin m → ℝ)
  (hf : DifferentiableAt ℝ f x) :
-- imply
  jacobianMatrix f x = LinearMap.toMatrix' (fderiv ℝ f x).toLinearMap := by
-- proof
  apply jacobianMatrix_eq_toMatrix'_fderiv f x hf


/--
[jacobianMatrix_fun_mulVec](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Calculus/Jacobian.lean)
-/
@[path]
private lemma jacobianMatrix_fun_mulVec_eq
-- given
  {m n : ℕ} (M : Matrix (Fin n) (Fin m) ℝ) (x : Fin m → ℝ) :
-- imply
  jacobianMatrix (fun y => M *ᵥ y) x = M := by
-- proof
  apply jacobianMatrix_fun_mulVec M x


/--
[jacobianMatrix_mulVec_eq_fderiv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Calculus/Jacobian.lean)
-/
@[path]
private lemma jacobianMatrix_mulVec_eq_fderiv_eq
-- given
  {m n : ℕ} (f : (Fin m → ℝ) → (Fin n → ℝ)) (x : Fin m → ℝ)
  (hf : DifferentiableAt ℝ f x) (v : Fin m → ℝ) :
-- imply
  (jacobianMatrix f x).mulVec v = fderiv ℝ f x v := by
-- proof
  apply jacobianMatrix_mulVec_eq_fderiv f x hf v


/--
[jacobianMatrix_comp](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Calculus/Jacobian.lean)
-/
@[path]
private lemma jacobianMatrix_comp_eq
-- given
  {m n p : ℕ} (f : (Fin m → ℝ) → (Fin n → ℝ)) (g : (Fin n → ℝ) → (Fin p → ℝ))
  (x : Fin m → ℝ)
  (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g (f x)) :
-- imply
  jacobianMatrix (g ∘ f) x =
    (jacobianMatrix g (f x)) * (jacobianMatrix f x) := by
-- proof
  apply jacobianMatrix_comp f g x hf hg


-- created on 2026-10-09
