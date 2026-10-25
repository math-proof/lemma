/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Calculus/Hessian.lean -/


import Theorem.Analysis.Calculus.Hessian
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
open MetaMathlibExt


-- Coordinate evaluations of the second Fréchet derivative agree after swapping directions.
example {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ 2 f)
    (x : Fin n → ℝ) (i j : Fin n) :
    fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1) =
      fderiv ℝ (fderiv ℝ f) x (Pi.single j 1) (Pi.single i 1) := by
  rw [← hessianMatrix_eq_fderiv_fderiv f hf x i j,
    ← hessianMatrix_eq_fderiv_fderiv f hf x j i]
  simpa [Matrix.transpose_apply] using
    (congrFun (congrFun (hessianMatrix_symmetric f hf x) i) j).symm

-- At a local minimum, a diagonal Hessian entry and its coordinate-line derivative are nonnegative.
example {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ 2 f)
    (x : Fin n → ℝ) (hmin : IsLocalMin f x) (i : Fin n) :
    0 ≤ hessianMatrix f x i i ∧
      0 ≤ deriv (deriv (fun t : ℝ => f (x + t • Pi.single i 1))) 0 := by
  classical
  have hquad :=
    isLocalMin_hessian_quadratic_nonneg f hf x hmin (Pi.single i (1 : ℝ))
  have hdiag : 0 ≤ hessianMatrix f x i i := by
    simpa [Pi.single_apply] using hquad
  refine ⟨hdiag, ?_⟩
  have hline : IsLocalMin (fun t : ℝ => f (x + t • Pi.single i 1)) 0 := by
    have hmin0 : IsLocalMin f (x + (0 : ℝ) • Pi.single i 1) := by simpa using hmin
    simpa [Function.comp_def] using hmin0.comp_continuous
      (g := fun t : ℝ => x + t • Pi.single i 1) (by fun_prop)
  exact hline.deriv_deriv_nonneg (by fun_prop)

-- The negative second derivative rules out a local minimum of cosine at zero.
example : ¬ IsLocalMin Real.cos 0 := by
  intro hmin
  have hnonneg :=
    hmin.deriv_deriv_nonneg (Real.contDiff_cos : ContDiff ℝ 2 Real.cos)
  have hsecond : deriv (deriv Real.cos) 0 = -1 := by
    rw [show deriv Real.cos = fun x => -Real.sin x by
      funext x
      exact (Real.hasDerivAt_cos x).deriv]
    change deriv (-Real.sin) 0 = -1
    rw [(Real.hasDerivAt_sin 0).neg.deriv]
    norm_num
  rw [hsecond] at hnonneg
  norm_num at hnonneg

-- The Hessian test detects a negative-curvature direction at the saddle point of `x * y`.
example : ¬ IsLocalMin (fun x : Fin 2 → ℝ => x 0 * x 1) 0 := by
  intro hmin
  have hf : ContDiff ℝ 2 (fun x : Fin 2 → ℝ => x 0 * x 1) := by fun_prop
  have hnonneg := isLocalMin_hessian_quadratic_nonneg
    (fun x : Fin 2 → ℝ => x 0 * x 1) hf 0 hmin ![1, -1]
  norm_num [Fin.sum_univ_two, hessianMatrix] at hnonneg

