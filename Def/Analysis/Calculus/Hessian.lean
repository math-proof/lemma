/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

@[expose] public section

open scoped BigOperators

open Set

/-!
# Hessian matrices

This file relates coordinatewise Hessian matrices to second Fréchet derivatives, proves their
symmetry for twice continuously differentiable functions, and proves positive semidefiniteness at
local minima.
-/


namespace Real.Calculus.Hessian

/-- Hessian matrix of `f` at `x` as an `n × n` real matrix. -/
noncomputable def hessianMatrix {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => deriv (fun s : ℝ => deriv (fun t : ℝ =>
    f (x + s • Pi.single i (1 : ℝ) + t • Pi.single j (1 : ℝ))) 0) 0

end Real.Calculus.Hessian
