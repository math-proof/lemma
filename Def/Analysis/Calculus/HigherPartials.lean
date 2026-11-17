/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

@[expose] public section

/-!
# Higher partial derivatives

This file relates coordinate partial derivatives to Fréchet derivatives and proves that mixed
second partial derivatives of a twice continuously differentiable real function commute.
-/


namespace Real.Calculus.HigherPartials

/-- Coordinate partial derivative of `f` along the `i`-th axis. -/
noncomputable def partialDeriv {n : ℕ} (f : (Fin n → ℝ) → ℝ) (i : Fin n) :
    (Fin n → ℝ) → ℝ :=
  fun x => deriv (fun t : ℝ => f (x + t • Pi.single i (1 : ℝ))) 0

end Real.Calculus.HigherPartials
