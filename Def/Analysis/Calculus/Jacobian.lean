module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

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

end Real.Calculus.Jacobian
