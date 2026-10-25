/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
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
