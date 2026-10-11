import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Jacobian matrices

This file relates coordinate Jacobian matrices to Fréchet derivatives and proves their chain rule.
-/

namespace Real.Calculus.Jacobian

open scoped Matrix

/-- Jacobian matrix of `f` at `x`: the `n × m` matrix of first partials.
Sources: `Mathlib/docs/undergrad.yaml`, section `Multivariable calculus` /
`Differential calculus`, entry `Jacobian matrix` (unmapped);
W. Rudin, Principles of Mathematical Analysis, 3rd ed., Ch. 9;
stable ref https://en.wikipedia.org/wiki/Jacobian_matrix_and_determinant. -/
noncomputable def jacobianMatrix {m n : ℕ} (f : (Fin m → ℝ) → (Fin n → ℝ))
    (x : Fin m → ℝ) : Matrix (Fin n) (Fin m) ℝ :=
  fun i j => deriv (fun t : ℝ => f (x + t • Pi.single j (1 : ℝ)) i) 0

/-- Characteristic spec: the `(i, j)` entry is the partial of component `i`
along the `j`-th coordinate axis.
Sources: `Mathlib/docs/undergrad.yaml`, section `Multivariable calculus` /
`Differential calculus`, entry `Jacobian matrix` (unmapped);
W. Rudin, Principles of Mathematical Analysis, 3rd ed., Ch. 9. -/
theorem jacobianMatrix_apply {m n : ℕ} (f : (Fin m → ℝ) → (Fin n → ℝ))
    (x : Fin m → ℝ) (i : Fin n) (j : Fin m) :
    jacobianMatrix f x i j =
      deriv (fun t : ℝ => f (x + t • Pi.single j (1 : ℝ)) i) 0 := rfl

private theorem jacobian_hasDerivAt_along_single {m n : ℕ}
    (f : (Fin m → ℝ) → (Fin n → ℝ)) (x : Fin m → ℝ)
    (hf : DifferentiableAt ℝ f x) (j : Fin m) :
    HasDerivAt (fun t : ℝ => f (x + t • Pi.single j (1 : ℝ)))
      (fderiv ℝ f x (Pi.single j (1 : ℝ))) 0 := by
  have hline : HasDerivAt (fun t : ℝ => x + t • Pi.single j (1 : ℝ))
      (Pi.single j (1 : ℝ)) 0 := by
    simpa using
      ((hasDerivAt_id' (0 : ℝ)).smul_const (Pi.single j (1 : ℝ))).const_add x
  simpa [Function.comp_def] using
    hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)

/-- At a differentiability point, a Jacobian entry is the corresponding coordinate of the
Fréchet derivative on a standard basis vector. -/
theorem jacobianMatrix_apply_of_differentiableAt {m n : ℕ}
    (f : (Fin m → ℝ) → (Fin n → ℝ)) (x : Fin m → ℝ)
    (hf : DifferentiableAt ℝ f x) (i : Fin n) (j : Fin m) :
    jacobianMatrix f x i j = fderiv ℝ f x (Pi.single j (1 : ℝ)) i := by
  rw [jacobianMatrix_apply]
  exact (hasDerivAt_pi.mp (jacobian_hasDerivAt_along_single f x hf j) i).deriv

/-- At a differentiability point, the Jacobian is the matrix of the Fréchet derivative. -/
theorem jacobianMatrix_eq_toMatrix'_fderiv {m n : ℕ}
    (f : (Fin m → ℝ) → (Fin n → ℝ)) (x : Fin m → ℝ)
    (hf : DifferentiableAt ℝ f x) :
    jacobianMatrix f x = LinearMap.toMatrix' (fderiv ℝ f x).toLinearMap := by
  ext i j
  rw [jacobianMatrix_apply_of_differentiableAt f x hf, LinearMap.toMatrix'_apply]
  rfl

/-- The Jacobian of a matrix acting by multiplication is the matrix itself at every point. -/
theorem jacobianMatrix_fun_mulVec {m n : ℕ}
    (M : Matrix (Fin n) (Fin m) ℝ) (x : Fin m → ℝ) :
    jacobianMatrix (fun y => M *ᵥ y) x = M := by
  let L : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ) :=
    LinearMap.toContinuousLinearMap (Matrix.mulVecLin M)
  change jacobianMatrix (fun y => L y) x = M
  ext i j
  rw [jacobianMatrix_apply_of_differentiableAt (fun y => L y) x L.differentiableAt]
  change (fderiv ℝ L x) (Pi.single j 1) i = M i j
  rw [L.fderiv]
  simp [L]

/-- The Jacobian matrix represents the Frechet derivative on coordinates.
Sources: `Mathlib/docs/undergrad.yaml`, section `Multivariable calculus` /
`Differential calculus`, entry `Jacobian matrix` (unmapped);
W. Rudin, Principles of Mathematical Analysis, 3rd ed., Ch. 9.

Proves `Wanted` entry `jacobianMatrix_mulVec_eq_fderiv`.

Proof: The Jacobian is the matrix of `fderiv` (Wikipedia, "Jacobian matrix and determinant":
it represents the total derivative), by `jacobianMatrix_eq_toMatrix'_fderiv`; then use
`LinearMap.toMatrix'_mulVec`.
-/
theorem jacobianMatrix_mulVec_eq_fderiv {m n : ℕ}
    (f : (Fin m → ℝ) → (Fin n → ℝ)) (x : Fin m → ℝ)
    (hf : DifferentiableAt ℝ f x) (v : Fin m → ℝ) :
    (jacobianMatrix f x).mulVec v = fderiv ℝ f x v := by
  rw [jacobianMatrix_eq_toMatrix'_fderiv f x hf, LinearMap.toMatrix'_mulVec]
  rfl

/-- Chain rule for Jacobian matrices.
Sources: `Mathlib/docs/undergrad.yaml`, section `Multivariable calculus` /
`Differential calculus`, entries `Jacobian matrix` and `chain rule`;
W. Rudin, Principles of Mathematical Analysis, 3rd ed., Theorem 9.15.

Proves `Wanted` entry `jacobianMatrix_comp`.

Proof: As in Wikipedia, "Jacobian matrix and determinant" (chain rule), rewrite the Jacobians as
matrices of Fréchet derivatives, then apply `fderiv_comp` and `LinearMap.toMatrix'_comp`.
-/
theorem jacobianMatrix_comp {m n p : ℕ}
    (f : (Fin m → ℝ) → (Fin n → ℝ)) (g : (Fin n → ℝ) → (Fin p → ℝ))
    (x : Fin m → ℝ)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g (f x)) :
    jacobianMatrix (g ∘ f) x =
      (jacobianMatrix g (f x)) * (jacobianMatrix f x) := by
  rw [jacobianMatrix_eq_toMatrix'_fderiv (g ∘ f) x (hg.comp x hf),
    jacobianMatrix_eq_toMatrix'_fderiv g (f x) hg,
    jacobianMatrix_eq_toMatrix'_fderiv f x hf,
    fderiv_comp x hg hf, ContinuousLinearMap.toLinearMap_comp,
    LinearMap.toMatrix'_comp]

end Real.Calculus.Jacobian
